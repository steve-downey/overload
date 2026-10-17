-- Overload/Outcome.lean                                              -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Std

/-!
# The two outcome types

Substitution and resolution each return more than success or failure, and
the theorems are about the difference.

`Subst` gains a fourth case, ill-formed with no diagnostic required, when
the single translation unit axiom is relaxed in phase 8.
-/

namespace Overload

/-- Why a substitution or a resolution did not succeed. -/
abbrev Reason := String

/-- The outcome of a substitution. -/
@[specification]
inductive Subst (α : Type) where
  /-- Substitution succeeded: the template parameters were replaced with
  the corresponding template arguments. -/
  | ok : α → Subst α
  /-- Deduction failure: the substitution produced an invalid type or
  expression in the immediate context. -/
  | soft : Reason → Subst α
  /-- Ill-formed, diagnostic required: the invalid type or expression was
  outside the immediate context. -/
  | hard : Reason → Subst α
  deriving Repr, DecidableEq, Inhabited

attribute [std rule "temp.deduct.general#6.sentence-1"] Subst.ok
attribute [std rule "temp.deduct.general#8.sentence-1"] Subst.soft
attribute [std rule "temp.deduct.general#8.sentence-3"] Subst.hard

namespace Subst

/-- Run the next step only after success; a failure of either kind stands. -/
def bind : Subst α → (α → Subst β) → Subst β
  | ok a, f => f a
  | soft r, _ => soft r
  | hard r, _ => hard r

instance : Monad Subst where
  pure := ok
  bind := bind

/-- Did it succeed? -/
def isOk : Subst α → Bool
  | ok _ => true
  | _ => false

/-- The value, when it succeeded. -/
def toOption : Subst α → Option α
  | ok a => some a
  | _ => none

/-- `pure` on `Subst` is `ok`. -/
@[simp]
theorem pure_eq (a : α) : (pure a : Subst α) = ok a := rfl

/-- `>>=` on `Subst` is `Subst.bind`, so the equations below apply to the
monadic spelling. -/
@[simp]
theorem bind_eq (s : Subst α) (f : α → Subst β) : s >>= f = Subst.bind s f := rfl

/-- A hard error is absorbing: nothing after it changes the outcome. -/
@[simp]
theorem bind_hard (r : Reason) (f : α → Subst β) : bind (hard r) f = hard r := rfl

/-- A deduction failure is absorbing too: a later step cannot turn a soft
failure into success, nor into a hard error. The step-order hazard is
the other direction, a hard error before a step that would have failed
softly, which `bind_hard` leaves standing. -/
@[simp]
theorem bind_soft (r : Reason) (f : α → Subst β) : bind (soft r) f = soft r := rfl

@[simp]
theorem bind_ok (a : α) (f : α → Subst β) : bind (ok a) f = f a := rfl

/-- Apply a function to the value of a success; a failure stands. -/
def map (f : α → β) : Subst α → Subst β
  | ok a => ok (f a)
  | soft r => soft r
  | hard r => hard r

/-- In monadic spelling: `hard r >>= f = hard r`. -/
theorem hard_absorbing (r : Reason) (f : α → Subst β) : (hard r >>= f) = hard r := rfl

/-- A chain of steps ends in a hard error if and only if some step produced
one and no earlier step had failed softly: the hard error is the first
failure. Stated for two steps; longer chains follow by `bind_hard`. -/
theorem bind_eq_hard_iff (s : Subst α) (f : α → Subst β) (r : Reason) :
    bind s f = hard r ↔ s = hard r ∨ ∃ a, s = ok a ∧ f a = hard r := by
  cases s with
  | ok a => simp
  | soft _ => simp
  | hard _ => simp

end Subst

/-- The outcome of overload resolution, or of instance lookup. -/
@[specification]
inductive Resolution (α : Type) where
  /-- Exactly one viable function is better than all the others: it is the
  one selected. -/
  | selected : α → Resolution α
  /-- No viable function: overload resolution fails and the invocation is
  ill-formed. The model keeps this as a value so that a missing instance
  can be a soft failure at the next layer up. -/
  | noMatch : Resolution α
  /-- More than one viable function and none better than all the others:
  the call is ill-formed, and the Standard makes that a defined outcome.
  Ambiguity is not a conflict. -/
  | ambiguous : List α → Resolution α
  /-- A candidate's deduction produced a hard error, so the program is
  ill-formed whatever the other candidates would have done. -/
  | illFormed : Reason → Resolution α
  deriving Repr, DecidableEq, Inhabited

attribute [std rule "over.match.best.general#3.sentence-1"] Resolution.selected
attribute [std rule "over.match.general#3.sentence-2"] Resolution.noMatch
attribute [std rule "over.match.best.general#3.sentence-1"] Resolution.ambiguous
attribute [std rule "temp.deduct.general#8.sentence-3"] Resolution.illFormed

namespace Resolution

/-- The selected candidate, when one was. -/
def toOption : Resolution α → Option α
  | selected a => some a
  | _ => none

/-- Map over the selected candidate, or the ambiguous ones. -/
def map (f : α → β) : Resolution α → Resolution β
  | selected a => selected (f a)
  | noMatch => noMatch
  | ambiguous as => ambiguous (as.map f)
  | illFormed r => illFormed r

end Resolution

end Overload
