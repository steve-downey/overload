-- Overload/Ordering.lean                                             -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Steps

/-!
# Partial ordering of function templates, and partial specialization matching

Partial ordering ([temp.func.order]) transforms each template by
substituting a unique synthesized type or value for each of its template
parameters, then deduces the other template's parameter types from the
transformed types ([temp.deduct.partial]). `F` is at least as specialized
as `G` when that deduction succeeds for every nominated type, less the
reference tie-breaks of [temp.deduct.partial]/9, which deny the opposite
direction. `F` is more specialized than `G` when it is at least as
specialized and `G` is not; when each is at least as specialized as the
other, the constraints decide, but only through the gate of
[temp.func.order]/8: equal-length parameter lists, equivalent template
parameters ([temp.over.link]/6), and the same function parameter types.
That gate is the plan's tie-break-reach suspect, and `tieBreak_needs_equal_heads`
is its lemma.

Partial specialization matching ([temp.spec.partial.match]) selects among
the partial specializations of a variable template by deduction, and
orders them by the rewrite of [temp.spec.partial.order]/1 to function
templates with a single parameter.

The exit criteria of phase 4: matching is deterministic, which
`patternMatches_iff` reduces to the determinism of deduction, and more-specialized
is irreflexive and asymmetric (`moreSpecialized_irrefl`,
`moreSpecialized_asymm`); transitivity is searched for a counterexample in
`OverloadTest/Ordering.lean`.
-/

namespace Overload

namespace PartialOrdering

/-! ## The transformed template -/

/-- The unique type synthesized for the type template parameter `i`. The
name cannot be spelled in C++, so it collides with nothing. -/
def synthType (i : ParamIdx) : Ty := .named s!"#U{i}"

/-- The unique value synthesized for the constant template parameter `i`:
a class value of a type no program names. -/
def synthValue (i : ParamIdx) : Ty := .value (.obj s!"#V{i}" .nil)

/-- The synthesized argument for each parameter of a head. -/
def synthBindings (h : Head) : Bindings :=
  h.zipIdx.map fun (p, i) =>
    match p.kind with
    | .type => (i, synthType i)
    | .const _ => (i, synthValue i)

/-- The transformed template: each template parameter replaced in the
nominated types by its synthesized type or value. -/
@[std rule "temp.func.order#3.sentence-1"]
def transform (h : Head) (tys : List Ty) : List Ty :=
  tys.map (Ty.subst (synthBindings h))

/-- The types used to determine the ordering: in the context of a call
with `m` arguments, the parameter types for which the call has arguments;
in other contexts, the function type, which on the fragment is the
parameter types. -/
@[std rule "temp.deduct.partial#3"]
def nominated (ft : FunctionTemplate) : Option Nat → List Ty
  | some m => ft.params.take m
  | none => ft.params

/-! ## Deduction for partial ordering -/

/-- Is the type `const`-qualified at the top? -/
def isConst : Ty → Bool
  | .const _ => true
  | _ => false

/-- Is the type an lvalue reference? -/
def isLref : Ty → Bool
  | .lref _ => true
  | _ => false

/-- One `P`/`A` pair, [temp.deduct.partial]/5 to /9. `P` is from the
parameter template, `A` from the transformed argument template. The
result is the bindings when deduction succeeds, so that `A`'s type is at
least as specialized as `P`'s, and the flag of /9: when the types are
identical after the transformations and both were references, an lvalue
reference `A` against a non-lvalue-reference `P`, or an `A` more
cv-qualified than `P`, means `P`'s type is not considered at least as
specialized as `A`'s. "Identical after the transformations" is read as
`P` with the deduced arguments substituted being `A`. -/
@[std rule "temp.deduct.partial#8.sentence-4"]
def deducePair (p a : Ty) (σ : Bindings) : Option Bindings × Bool :=
  let pRef := p.isRef
  let aRef := a.isRef
  let p₁ := p.referred
  let a₁ := a.referred
  let aMoreCv := pRef && aRef && isConst a₁ && !isConst p₁
  let p₂ := p₁.stripConst
  let a₂ := a₁.stripConst
  match deduceTy p₂ a₂ σ with
  | some σ' =>
    let identical := p₂.subst σ' == a₂
    let deny := identical && pRef && aRef && ((isLref a && !isLref p) || aMoreCv)
    (some σ', deny)
  | none => (none, false)

/-- The /9 denial for a pair, on its own. -/
@[std rule "temp.deduct.partial#9"]
def denies (p a : Ty) : Bool := (deducePair p a []).2

/-- The template parameters a list of types uses, a parameter in a
non-deduced context counting as used. -/
def usedParams : Ty → List ParamIdx
  | .named _ | .nil => []
  | .param i => [i]
  | .const t | .ptr t | .lref t | .rref t | .nondeduced t | .lookup _ t | .spec _ t => usedParams t
  | .cons a as => usedParams a ++ usedParams as
  | .value v => usedVal v
where
  usedVal : Val → List ParamIdx
    | .int _ | .bool _ | .nil => []
    | .obj _ vs => usedVal vs
    | .cons v vs => usedVal v ++ usedVal vs
    | .param i => [i]

/-- Deduce every nominated pair in turn, the bindings shared; a template
parameter may remain without a value only if the nominated types do not
use it. -/
@[std rule "temp.deduct.partial#12.sentence-1"]
def deduceAll (ps as : List Ty) : Bool :=
  if ps.length != as.length then false
  else
    match go (ps.zip as) [] with
    | some σ => (ps.flatMap usedParams).all fun i => (σ.lookup i).isSome
    | none => false
where
  go : List (Ty × Ty) → Bindings → Option Bindings
    | [], σ => some σ
    | (p, a) :: rest, σ =>
      match deducePair p a σ with
      | (some σ', _) => go rest σ'
      | (none, _) => none

/-- Deduction with `f` transformed as the argument template and `g` as
the parameter template, in a context. The first component says the
deduction succeeded for every nominated type, so `f` is at least as
specialized as `g` by [temp.deduct.partial]/8 and /10; the second says
some pair denies the opposite direction by /9. -/
@[std rule "temp.deduct.partial#2.sentence-3"]
def direction (f g : FunctionTemplate) (ctx : Option Nat) : Bool × Bool :=
  let as := transform f.head (nominated f ctx)
  let ps := nominated g ctx
  (deduceAll ps as, (ps.zip as).any fun (p, a) => denies p a)

/-- `F` is at least as specialized as `G`: for each nominated pair the
type from `F` is at least as specialized as the type from `G`, and no
pair of the opposite direction denies it. -/
@[std rule "temp.deduct.partial#10.sentence-1"]
def atLeastAsSpecialized (f g : FunctionTemplate) (ctx : Option Nat) : Bool :=
  (direction f g ctx).1 && !(direction g f ctx).2

/-- `F` is more specialized than `G` by deduction alone: at least as
specialized, and `G` not at least as specialized as `F`. -/
@[std rule "temp.deduct.partial#10.sentence-2"]
def moreSpecializedByDeduction (f g : FunctionTemplate) (ctx : Option Nat) : Bool :=
  atLeastAsSpecialized f g ctx && !atLeastAsSpecialized g f ctx

/-! ## The tie-break of [temp.func.order]/8 -/

/-- Erase the type-constraints on placeholder types: a constrained
placeholder `shape auto`, spelled `Ty.spec "auto" (args [shape])`, becomes
plain `auto`. -/
def erasePlaceholderConstraints : Ty → Ty
  | .spec "auto" _ => .named "auto"
  | .spec c as => .spec c (erasePlaceholderConstraints as)
  | .const t => .const (erasePlaceholderConstraints t)
  | .ptr t => .ptr (erasePlaceholderConstraints t)
  | .lref t => .lref (erasePlaceholderConstraints t)
  | .rref t => .rref (erasePlaceholderConstraints t)
  | .cons a as => .cons (erasePlaceholderConstraints a) (erasePlaceholderConstraints as)
  | .nondeduced t => .nondeduced (erasePlaceholderConstraints t)
  | .lookup n a => .lookup n (erasePlaceholderConstraints a)
  | t => t

/-- Two template parameters are equivalent: the same kind, and for
constant template parameters equivalent types ignoring the use of
type-constraints for placeholder types. The fragment has no packs and no
template template parameters. -/
@[std rule "temp.over.link#6.sentence-2"]
def paramEquivalent (p q : TemplateParam) : Bool :=
  match p.kind, q.kind with
  | .type, .type => true
  | .const t, .const u => erasePlaceholderConstraints t == erasePlaceholderConstraints u
  | _, _ => false

/-- Corresponding template parameters of two lists are equivalent. -/
def headsEquivalent (h₁ h₂ : Head) : Bool :=
  h₁.length == h₂.length && (h₁.zip h₂).all fun (p, q) => paramEquivalent p q

/-- The gate: constraints are compared only when the template parameter
lists and the function parameter lists have the same length, the
corresponding template parameters are equivalent, and the positionally
corresponding function parameters have the same type. No rewritten
candidates and no conversion functions in the fragment. -/
@[std rule "temp.func.order#8"]
def tieBreakApplies (f g : FunctionTemplate) : Bool :=
  f.head.length == g.head.length && f.params.length == g.params.length &&
    headsEquivalent f.head g.head && f.params == g.params

/-- Partial ordering: `F` is more specialized than `G` by deduction, or
each is at least as specialized as the other, the gate is open, and `F`
is more constrained. -/
@[std rule "temp.func.order#2.sentence-4"]
def moreSpecialized (ctx : Option Nat) (f g : FunctionTemplate) : Bool :=
  let fg := atLeastAsSpecialized f g ctx
  let gf := atLeastAsSpecialized g f ctx
  (fg && !gf) || (fg && gf && tieBreakApplies f g && Constraint.moreConstrained f.constraint g.constraint)

/-! ## The order's shape -/

/-- Nothing is more specialized than itself. -/
theorem moreSpecialized_irrefl (ctx : Option Nat) (f : FunctionTemplate) :
    moreSpecialized ctx f f = false := by
  simp [moreSpecialized, Constraint.moreConstrained_irrefl]

/-- More specialized is asymmetric: it is a strict order as far as
irreflexivity and asymmetry go. -/
theorem moreSpecialized_asymm (ctx : Option Nat) (f g : FunctionTemplate)
    (h : moreSpecialized ctx f g = true) : moreSpecialized ctx g f = false := by
  simp only [moreSpecialized, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨hfg, hgf⟩ | ⟨⟨⟨hfg, hgf⟩, _⟩, hc⟩
  · simp [moreSpecialized, hfg, hgf]
  · simp [moreSpecialized, hfg, hgf, Constraint.moreConstrained_asymm _ _ hc]

/-- The tie-break-reach lemma: template parameter lists of different
lengths switch the constraint comparison off, so only deduction can
order the pair. -/
@[std theorem "temp.func.order#8"]
theorem tieBreak_needs_equal_heads (ctx : Option Nat) (f g : FunctionTemplate)
    (h : f.head.length ≠ g.head.length) :
    moreSpecialized ctx f g = moreSpecializedByDeduction f g ctx := by
  have : tieBreakApplies f g = false := by
    simp [tieBreakApplies, h]
  simp [moreSpecialized, moreSpecializedByDeduction, this]

/-- Constant template parameters of different types switch the constraint
comparison off too. -/
theorem tieBreak_needs_equivalent_params (ctx : Option Nat) (f g : FunctionTemplate)
    (h : headsEquivalent f.head g.head = false) :
    moreSpecialized ctx f g = moreSpecializedByDeduction f g ctx := by
  have : tieBreakApplies f g = false := by
    simp [tieBreakApplies, h]
  simp [moreSpecialized, moreSpecializedByDeduction, this]

/-! ## Partial specialization matching -/

/-- The rewrite of [temp.spec.partial.order]/1: a partial specialization of
`tc` with head `h` and argument `pattern` becomes a function template with
the same head and a single parameter of type `tc<pattern>`. -/
@[std rule "temp.spec.partial.order#1.sentence-1"]
def rewrite (tc : String) (h : Head) (pattern : Ty) : FunctionTemplate :=
  { name := tc, head := h, params := [.spec' tc [pattern]] }

/-- A partial specialization matches an argument when its template
arguments can be deduced from it. The fragment's instances carry no
constraints. -/
@[std rule "temp.spec.partial.match#2.sentence-1"]
def patternMatches (h : Head) (pattern arg : Ty) : Bool :=
  match deduceTy pattern arg [] with
  | some σ => allDeduced h.length σ
  | none => false

/-- The specification form of `patternMatches`: the template arguments are
deduced, and every parameter of the head has one. -/
def PatternMatches (h : Head) (pattern arg : Ty) : Prop :=
  ∃ σ, DeduceTy pattern arg [] σ ∧ allDeduced h.length σ = true

/-- Matching is deterministic: the relation and the function agree, by
the agreement and determinism of deduction. -/
theorem patternMatches_iff (h : Head) (pattern arg : Ty) : PatternMatches h pattern arg ↔ patternMatches h pattern arg = true := by
  constructor
  · rintro ⟨σ, hd, ha⟩
    simp [patternMatches, deduceTy_complete hd, ha]
  · intro hm
    unfold patternMatches at hm
    split at hm
    · exact ⟨_, deduceTy_sound _ _ _ _ ‹_›, hm⟩
    · exact absurd hm (by simp)

/-- Among a variable template's partial specializations, given by head and
argument in declaration order, the one an argument selects: the single
match, the most specialized of several matches, `ambiguous` when none is
more specialized than all the others, and `noMatch` when the primary
template is used. -/
@[std rule "temp.spec.partial.match#1"]
def select (tc : String) (insts : List (Head × Ty)) (arg : Ty) : Resolution Nat :=
  let ms := insts.zipIdx.filter fun ((h, pat), _) => patternMatches h pat arg
  match ms with
  | [] => .noMatch
  | [(_, i)] => .selected i
  | _ =>
    let best := ms.filter fun ((h, pat), i) => ms.all fun ((h', pat'), j) =>
      i == j || moreSpecialized none (rewrite tc h pat) (rewrite tc h' pat')
    match best with
    | [(_, i)] => .selected i
    | _ => .ambiguous (ms.map (·.2))

end PartialOrdering

end Overload
