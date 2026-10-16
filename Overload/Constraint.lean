-- Overload/Constraint.lean                                           -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Syntax
import Overload.Outcome

/-!
# Constraints, as far as the step order needs them

Phase 3 builds normalization, atomic identity and subsumption. The step
order of [temp.deduct.general]/5 needs only satisfaction: whether the
associated constraints of a function template hold for the deduced
arguments. An atomic constraint is an expression the model does not look
inside, so the environment answers it as an oracle, after the parameter
mapping has been substituted.
-/

namespace Overload

/-- A constraint in normal form: atomic constraints joined by conjunction
and disjunction. An atomic constraint is an expression, named, with its
parameter mapping. -/
inductive Constraint where
  | atomic (expr : String) (mapping : List Ty)
  | conj (left right : Constraint)
  | disj (left right : Constraint)
  deriving Repr, DecidableEq, Inhabited

namespace Constraint

/-- The oracle for an atomic constraint: given the expression and the
substituted targets of its mapping, whether it is valid and `true`. A
`soft` answer is an invalid substitution in the immediate context. -/
abbrev Oracle := String → List Ty → Subst Bool

/-- Satisfaction. For an atomic constraint the mapping is substituted into
the expression, an invalid result in the immediate context means not
satisfied, and otherwise the expression's value decides. Conjunction checks
its right operand only when the left is satisfied, and disjunction only
when the left is not. -/
@[std rule "temp.constr.atomic#3.sentence-1"]
def satisfied (oracle : Oracle) (σ : Bindings) : Constraint → Subst Bool
  | atomic e m =>
    match oracle e (m.map (Ty.subst σ)) with
    | .soft _ => .ok false
    | r => r
  | conj l r => do
    if ← satisfied oracle σ l then satisfied oracle σ r else pure false
  | disj l r => do
    if ← satisfied oracle σ l then pure true else satisfied oracle σ r

/-- An invalid substitution in an atomic constraint's immediate context is
"not satisfied", never a deduction failure of its own. -/
@[std rule "temp.constr.atomic#3.sentence-2"]
theorem satisfied_atomic_soft (oracle : Oracle) (σ : Bindings) (e : String) (m : List Ty)
    (r : Reason) (h : oracle e (m.map (Ty.subst σ)) = .soft r) :
    satisfied oracle σ (atomic e m) = .ok false := by
  simp [satisfied, h]

/-! ## Subsumption -/

/-- An atomic constraint, as a clause element: the expression and the
targets of its parameter mapping. -/
abbrev Atomic := String × List Ty

/-- Two atomic constraints are identical when they are formed from the
same appearance of the same expression and their parameter mappings
have the same targets. The fragment has no concept-ids to expand, so an
expression is identified by its name, and the targets compare as
template-ids do: structurally. -/
@[std rule "temp.constr.atomic#2.sentence-1"]
def identical (a b : Atomic) : Bool := a == b

/-- The disjunctive normal form: a disjunction of clauses, each a
conjunction of atomic constraints. -/
@[std rule "temp.constr.order#1"]
def dnf : Constraint → List (List Atomic)
  | atomic e m => [[(e, m)]]
  | disj l r => dnf l ++ dnf r
  | conj l r => (dnf l).flatMap fun p => (dnf r).map fun q => p ++ q

/-- The conjunctive normal form: a conjunction of clauses, each a
disjunction of atomic constraints. -/
@[std rule "temp.constr.order#1"]
def cnf : Constraint → List (List Atomic)
  | atomic e m => [[(e, m)]]
  | conj l r => cnf l ++ cnf r
  | disj l r => (cnf l).flatMap fun p => (cnf r).map fun q => p ++ q

/-- `P` subsumes `Q` if and only if every disjunctive clause of `P`'s
disjunctive normal form subsumes every conjunctive clause of `Q`'s
conjunctive normal form, where a disjunctive clause subsumes a
conjunctive clause when some atomic constraint of the first is identical
to some atomic constraint of the second. -/
@[std rule "temp.constr.order#1.sentence-1"]
def subsumes (p q : Constraint) : Bool :=
  (dnf p).all fun pi => (cnf q).all fun qj =>
    pi.any fun a => qj.any fun b => identical a b

/-- `D1` is at least as constrained as `D2` if both are constrained and
`D1`'s constraints subsume `D2`'s, or `D2` has none. Every constraint of
the fragment is eligible for subsumption. -/
@[std rule "temp.constr.order#4"]
def atLeastAsConstrained : Option Constraint → Option Constraint → Bool
  | _, none => true
  | some p, some q => subsumes p q
  | none, some _ => false

/-- `D1` is more constrained than `D2`: at least as constrained, and not
the other way round. -/
@[std rule "temp.constr.order#5"]
def moreConstrained (c₁ c₂ : Option Constraint) : Bool :=
  atLeastAsConstrained c₁ c₂ && !atLeastAsConstrained c₂ c₁

/-- Nothing is more constrained than itself. -/
theorem moreConstrained_irrefl (c : Option Constraint) : moreConstrained c c = false := by
  simp [moreConstrained]

/-- More constrained is asymmetric. -/
theorem moreConstrained_asymm (c₁ c₂ : Option Constraint) (h : moreConstrained c₁ c₂ = true) :
    moreConstrained c₂ c₁ = false := by
  simp only [moreConstrained, Bool.and_eq_true, Bool.not_eq_true'] at h
  simp [moreConstrained, h.1, h.2]

end Constraint

end Overload
