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

end Constraint

end Overload
