-- Overload/Dispatch.lean                                             -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Sfinae

/-!
# dispatch-styles

The plan's dispatch-styles target: for one ordered list of conditions,
the constraint-exclusion, if-constexpr and priority-tag encodings select
the same candidate, and differ only in whether having no candidate is a
soft or a hard failure.

The three encodings, for conditions `c₀, c₁, c₂` on `T`, preferred in
that order:

* constraint exclusion: overload `i` requires the negation of each
  earlier condition, then its own, `(!c₀<T>) && ... && cᵢ<T>`;
* priority tags: overload `i` requires `cᵢ<T>` and takes the tag
  `rank<2 - i>`, and the call passes `rank<2>`, so a nearer base wins;
* if-constexpr: one template whose body tests the conditions in order
  and ends in a `static_assert` (`ifConstexpr`).

The check is exhaustive over the eight valuations of three conditions
(`dispatch_styles`), not a theorem for every length. All three select the
first condition that holds. With none, exclusion and tags leave the call
not viable, a soft failure, and if-constexpr makes it ill-formed.

They differ in one more way, which the plan did not predict: which
conditions are evaluated. if-constexpr stops at the first that holds,
and so does exclusion, written negations first, since a conjunction is
checked left to right. Priority tags check every overload's condition.
A later condition whose checking fails hard leaves the first two
well-formed and makes the tagged call ill-formed (`dispatch_hard_condition`).
-/

namespace Overload

/-- The if-constexpr encoding: test the conditions in order, stopping at
the first that holds. A condition is a constant expression here, so a
failure in checking it is a hard error. None holding reaches the final
`static_assert`, a hard error too. -/
@[std rule "stmt.if#2.sentence-2"]
def ifConstexpr (env : Env) (σ : Bindings) : List Constraint → Nat → Subst Nat
  | [], _ => .hard "no branch of the if constexpr chain is taken"
  | c :: cs, i => do
    if ← Constraint.satisfied env.atomic σ c then return i
    else ifConstexpr env σ cs (i + 1)

/-- The first index whose condition holds. -/
def firstTrue (bs : List Bool) : Option Nat := bs.findIdx? id

private def T : Ty := .param 0
private def X : Ty := .named "X"
private def typeParam : TemplateParam := { kind := .type }

/-- The three conditions, as atomic constraints on `T`. -/
def cond (i : Nat) : Constraint := .atomic s!"c{i}" [T]

/-- The negation of a condition, an atomic constraint of its own. -/
def notCond (i : Nat) : Constraint := .atomic s!"!c{i}" [T]

/-- The concepts the conditions name, for the emitted C++: each holds or
not for every type, as the valuation says. -/
def condConcepts (bs : List Bool) : List Decl :=
  bs.zipIdx.map fun (b, i) => .concept s!"c{i}" (if b then "true" else "false")

/-- The truth of each condition and its negation at `X`. -/
def condAtomics (bs : List Bool) : List (String × List Ty × Bool) :=
  bs.zipIdx.flatMap fun (b, i) => [(s!"c{i}", [X], b), (s!"!c{i}", [X], !b)]

/-- Constraint exclusion over three conditions, the last of them `last`. -/
def exclusionProgram (bs : List Bool) (last : Constraint := cond 2) : Program :=
  [.class "X"] ++ condConcepts bs ++
    [ .functionTemplate { name := "g", head := [typeParam], params := [T], constraint := some (cond 0) }
    , .functionTemplate { name := "g", head := [typeParam], params := [T]
                          constraint := some (.conj (notCond 0) (cond 1)) }
    , .functionTemplate { name := "g", head := [typeParam], params := [T]
                          constraint := some (.conj (notCond 0) (.conj (notCond 1) last)) } ]

private def rank (i : Nat) : Ty := .named s!"rank{i}"

/-- Priority tags over three conditions, the last of them `last`. -/
def tagsProgram (bs : List Bool) (last : Constraint := cond 2) : Program :=
  [ .class "X", .class "rank0", .class "rank1" [rank 0], .class "rank2" [rank 1] ] ++ condConcepts bs ++
    [ .functionTemplate { name := "g", head := [typeParam], params := [T, rank 2], constraint := some (cond 0) }
    , .functionTemplate { name := "g", head := [typeParam], params := [T, rank 1], constraint := some (cond 1) }
    , .functionTemplate { name := "g", head := [typeParam], params := [T, rank 0], constraint := some last } ]

/-- The exclusion call. -/
def exclusionCall (p : Program) (atomics : List (String × List Ty × Bool)) : Resolution Nat :=
  (invoke .text (Env.ofProgram p atomics) p.ranking (p.candidates "g") [{ ty := X }]).map (·.index)

/-- The tagged call, `g(x, rank2{})`. -/
def tagsCall (p : Program) (atomics : List (String × List Ty × Bool)) : Resolution Nat :=
  (invoke .text (Env.ofProgram p atomics) p.ranking (p.candidates "g")
    [{ ty := X }, { ty := rank 2 }]).map (·.index)

/-- The branch the if-constexpr chain takes for `T = X`. -/
def ifConstexprBranch (p : Program) (atomics : List (String × List Ty × Bool))
    (conds : List Constraint) : Subst Nat :=
  ifConstexpr (Env.ofProgram p atomics) [(0, X)] conds 0

/-- What the plan expects of a resolution: the first condition that
holds, or no viable function. -/
def expectedCall (bs : List Bool) : Resolution Nat :=
  match firstTrue bs with
  | some i => .selected i
  | none => .noMatch

/-- dispatch-styles, over the eight valuations of three conditions:
exclusion and priority tags select the first condition that holds, or
find no viable function; the if-constexpr chain takes that branch, or is
ill-formed. -/
theorem dispatch_styles (b₀ b₁ b₂ : Bool) :
    let bs := [b₀, b₁, b₂]
    exclusionCall (exclusionProgram bs) (condAtomics bs) = expectedCall bs ∧
      tagsCall (tagsProgram bs) (condAtomics bs) = expectedCall bs ∧
      (match firstTrue bs with
        | some i => ifConstexprBranch (exclusionProgram bs) (condAtomics bs) [cond 0, cond 1, cond 2] = .ok i
        | none => ∃ e, ifConstexprBranch (exclusionProgram bs) (condAtomics bs)
            [cond 0, cond 1, cond 2] = .hard e) := by
  cases b₀ <;> cases b₁ <;> cases b₂ <;> exact ⟨rfl, rfl, by first | rfl | exact ⟨_, rfl⟩⟩

/-- The last condition names a lookup whose primary fails hard. -/
def hardLast : Constraint := .atomic "lookup_formed" [.named "functor", T]

/-- With the first condition holding and the last failing hard when
checked: exclusion and if-constexpr never check the last and select the
first; priority tags check every overload's condition and make the call
ill-formed. -/
theorem dispatch_hard_condition :
    let bs := [true, false, false]
    let ex := .lookupHard "functor" :: exclusionProgram bs hardLast
    let tg := .lookupHard "functor" :: tagsProgram bs hardLast
    exclusionCall ex (condAtomics bs) = .selected 0 ∧
      ifConstexprBranch ex (condAtomics bs) [cond 0, cond 1, hardLast] = .ok 0 ∧
      ∃ e, tagsCall tg (condAtomics bs) = .illFormed e :=
  ⟨rfl, rfl, ⟨_, rfl⟩⟩

end Overload
