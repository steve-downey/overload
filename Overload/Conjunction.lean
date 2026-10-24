-- Overload/Conjunction.lean                                          -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Steps

/-!
# A conjunction of atomic constraints

Satisfaction of a conjunction checks its operands left to right and stops
at the first that is not satisfied ([temp.constr.op]/2). For a constraint
written as a conjunction of atomic constraints, in the order written, that
makes the constraint step a function of the atomic answers read in order
(`satisfied_conjunctionOf`, `conjunction_answers`): every answer valid and
true, the step passes; otherwise the first answer that is not decides, and
nothing after it is consulted. A hard error in a conjunct that is never
reached does not count. When no conjunct is a hard error to check, neither
is the conjunction (`conjunction_no_hard`).

This is what lets a constraint written as the member calls a body makes
answer as those calls do, which the typeclass side states for an algorithm
over an instance (`Overload/Typeclass/Members.lean`).
-/

namespace Overload

def conjunctionOf : Constraint.Atomic → List Constraint.Atomic → Constraint
  | a, [] => Constraint.ofAtomic a
  | a, b :: bs => .conj (Constraint.ofAtomic a) (conjunctionOf b bs)

/-- The answer of each atomic constraint, once the deduced arguments are
substituted. -/
def answers (oracle : Constraint.Oracle) (σ : Bindings) (calls : List Constraint.Atomic) :
    List (Subst Bool) :=
  calls.map (Constraint.answer oracle σ)

/-- How a conjunction reads the answers of its atomic constraints: left to
right, stopping at the first that is not valid and true. -/
def answersAll : List (Subst Bool) → Subst Bool
  | [] => .ok true
  | v :: vs =>
    match Constraint.atomicAnswer v with
    | .ok true => answersAll vs
    | r => r

/-- What the constraint step makes of that reading. The reading is never
`soft`, since an invalid atomic constraint is read as not satisfied. -/
def conjunctionOutcome (σ : Bindings) : Subst Bool → Subst Bindings
  | .ok true => .ok σ
  | .ok false => .soft "associated constraints not satisfied"
  | .soft r => .soft r
  | .hard r => .hard r

/-- A conjunction of atomic constraints is satisfied as their answers are
read in order: the first is checked, and the rest only if it is
satisfied. -/
@[std theorem "temp.constr.op#2.sentence-3"]
theorem satisfied_conjunctionOf (oracle : Constraint.Oracle) (σ : Bindings) (a : Constraint.Atomic)
    (as : List Constraint.Atomic) :
    Constraint.satisfied oracle σ (conjunctionOf a as) = answersAll (answers oracle σ (a :: as)) := by
  induction as generalizing a with
  | nil =>
    simp only [conjunctionOf, answers, List.map, answersAll, Constraint.satisfied_ofAtomic]
    cases Constraint.atomicAnswer (Constraint.answer oracle σ a) with
    | ok b => cases b <;> rfl
    | soft _ => rfl
    | hard _ => rfl
  | cons b bs ih =>
    simp only [conjunctionOf, Constraint.satisfied, Subst.bind_eq]
    rw [ih b, Constraint.satisfied_ofAtomic]
    simp only [answers, List.map, answersAll]
    cases Constraint.atomicAnswer (Constraint.answer oracle σ a) with
    | ok v => cases v <;> rfl
    | soft _ => rfl
    | hard _ => rfl

theorem constraintStep_conjunctionOf (env : Env) (a : Constraint.Atomic) (as : List Constraint.Atomic)
    (σ : Bindings) :
    constraintStep env (some (conjunctionOf a as)) σ =
      conjunctionOutcome σ (answersAll (answers env.atomic σ (a :: as))) := by
  simp only [constraintStep, satisfied_conjunctionOf, Subst.bind_eq]
  cases answersAll (answers env.atomic σ (a :: as)) with
  | ok v => cases v <;> rfl
  | soft _ => rfl
  | hard _ => rfl

theorem answersAll_prefix (pre post : List (Subst Bool)) (v : Subst Bool)
    (hpre : ∀ u ∈ pre, u = .ok true) :
    answersAll (pre ++ v :: post) = answersAll (v :: post) := by
  induction pre with
  | nil => rfl
  | cons u us ih =>
    have hu : u = .ok true := hpre u (List.mem_cons_self ..)
    subst hu
    simp only [List.cons_append, answersAll, Constraint.atomicAnswer]
    exact ih fun w hw => hpre w (List.mem_cons_of_mem _ hw)

theorem answersAll_true (vs : List (Subst Bool)) (h : ∀ v ∈ vs, v = .ok true) :
    answersAll vs = .ok true := by
  induction vs with
  | nil => rfl
  | cons u us ih =>
    have hu : u = .ok true := h u (List.mem_cons_self ..)
    subst hu
    simp only [answersAll, Constraint.atomicAnswer]
    exact ih fun w hw => h w (List.mem_cons_of_mem _ hw)

section conjunction

variable (env : Env) (a : Constraint.Atomic) (as : List Constraint.Atomic) (σ : Bindings)

/-- A conjunction of atomic constraints answers as its atomic constraints
do. Every one valid and true, the constraint step passes. Otherwise the
first that is not decides: not valid or false, a constraint not
satisfied; a hard error, a hard error. Nothing a later conjunct answers
is consulted. -/
theorem conjunction_answers :
    let r := constraintStep env (some (conjunctionOf a as)) σ
    let vs := answers env.atomic σ (a :: as)
    ((∀ v ∈ vs, v = .ok true) → r = .ok σ) ∧
    (∀ pre v post, vs = pre ++ v :: post → (∀ u ∈ pre, u = .ok true) →
      (v = .ok false ∨ ∃ e, v = .soft e) → ∃ e, r = .soft e) ∧
    (∀ pre e post, vs = pre ++ .hard e :: post → (∀ u ∈ pre, u = .ok true) → r = .hard e) := by
  intro r vs
  have hr : r = conjunctionOutcome σ (answersAll vs) := constraintStep_conjunctionOf env a as σ
  refine ⟨fun h => ?_, fun pre v post hvs hpre hv => ?_, fun pre e post hvs hpre => ?_⟩
  · rw [hr, answersAll_true vs h]; rfl
  · rw [hr, hvs, answersAll_prefix pre post v hpre]
    rcases hv with h | ⟨e, h⟩ <;> (subst h; exact ⟨_, rfl⟩)
  · rw [hr, hvs, answersAll_prefix pre post _ hpre]; rfl

/-- When no conjunct is a hard error to check, neither is the conjunction:
the constraint step passes or the constraint is not satisfied. -/
theorem conjunction_no_hard (h : ∀ v ∈ answers env.atomic σ (a :: as), ∀ e, v ≠ .hard e) :
    ∀ e, constraintStep env (some (conjunctionOf a as)) σ ≠ .hard e := by
  intro e
  rw [constraintStep_conjunctionOf]
  generalize answers env.atomic σ (a :: as) = vs at h
  suffices hs : ∀ e, answersAll vs ≠ .hard e by
    cases hv : answersAll vs with
    | ok b => cases b <;> simp [conjunctionOutcome]
    | soft _ => simp [conjunctionOutcome]
    | hard r => exact absurd hv (hs r)
  induction vs with
  | nil => simp [answersAll]
  | cons v vs ih =>
    intro e'
    have hv := h v (List.mem_cons_self ..)
    have ih' := ih fun w hw => h w (List.mem_cons_of_mem _ hw)
    cases v with
    | ok b => cases b <;> simp [answersAll, Constraint.atomicAnswer, ih']
    | soft _ => simp [answersAll, Constraint.atomicAnswer]
    | hard r => exact absurd rfl (hv r)

end conjunction

end Overload
