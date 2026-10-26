-- Overload/Lookup.lean                                               -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Program
import Overload.Ordering

/-!
# Variable template lookup over a program

A variable template with partial specializations, `trait<T>`, is a lookup:
instantiating it for a type selects among the partial specializations the
program declares, by partial specialization matching
([temp.spec.partial.match]) over the rewrite of [temp.spec.partial.order]/1.
The model calls the variable template a lookup and its partial
specializations instances, because that is what the typeclass encoding
uses them for, but nothing here is about typeclasses. Two theorems about
`PartialOrdering.select` hold for any such variable template:

* coherence: lookup selects a partial specialization exactly when it is
  the most specialized match, and at most one is; otherwise it reports
  the primary or ambiguity, and it never chooses silently (`coherence`,
  `MostSpecialized` and `mostSpecialized_unique`);
* stability: declaring one more partial specialization, anywhere in the
  program, leaves lookup unchanged at every type the new one does not
  match, and at a type it does match the lookup keeps its answer, moves
  to the new specialization, or becomes ambiguous (`stability`). Lookups
  of other variable templates do not move at all
  (`stability_other_typeclass`).

Neither theorem needs the single translation unit assumption or a soft
primary. Both are about the variable template, where a missing
specialization is the primary; those hypotheses enter at the call surface,
where a lookup is instantiated and its outcome becomes soft or hard.

Partial specializations are named by position among those of their
variable template, so inserting one shifts the positions after it;
`shiftAt` is that shift.
-/

namespace Overload

open PartialOrdering

namespace Program

/-- The partial specializations of a lookup in a program, as head and
pattern, in declaration order. -/
def instancesOf (p : Program) (tc : String) : List (Head × Ty) :=
  p.filterMap fun
    | .instance c h pat _ => if c = tc then some (h, pat) else none
    | _ => none

/-- Which partial specialization of `tc` the type `a` selects, by partial
specialization matching and ordering: lookup. -/
def selectInstance (p : Program) (tc : String) (a : Ty) : Resolution Nat :=
  select tc (p.instancesOf tc) a

/-- The type the selected instance declares its value to have, at the
argument, with the pattern's deduced arguments substituted; `none` when
no instance is selected or the selected one declares no value type. -/
def instanceValueType? (p : Program) (tc : String) (a : Ty) : Option Ty :=
  match p.selectInstance tc a with
  | .selected i =>
    match (p.filter (isInstanceOf tc))[i]? with
    | some (.instance _ _ pat (some v)) => (deduceTy pat a []).map fun σ => v.subst σ
    | _ => none
  | _ => none

theorem instancesOf_insert (p₁ p₂ : Program) (tc : String) (h : Head) (pat : Ty) :
    instancesOf (p₁ ++ .instance tc h pat :: p₂) tc = instancesOf p₁ tc ++ (h, pat) :: instancesOf p₂ tc := by
  simp [instancesOf, List.filterMap_append]

theorem instancesOf_append (p₁ p₂ : Program) (tc : String) :
    instancesOf (p₁ ++ p₂) tc = instancesOf p₁ tc ++ instancesOf p₂ tc := by
  simp [instancesOf, List.filterMap_append]

theorem instancesOf_insert_other (p₁ p₂ : Program) (tc tc' : String) (h : Head) (pat : Ty)
    (hne : tc ≠ tc') :
    instancesOf (p₁ ++ .instance tc h pat :: p₂) tc' = instancesOf (p₁ ++ p₂) tc' := by
  simp [instancesOf, List.filterMap_append, hne]

end Program

/-! ## Coherence -/

/-- Coherence: lookup selects a partial specialization exactly when it is
the most specialized of those that match. With `mostSpecialized_unique`,
at most one is ever a candidate for selection, and with
`selectInstance_ne_illFormed` every other outcome is the primary or a
reported ambiguity. -/
theorem coherence (p : Program) (tc : String) (a : Ty) (i : Nat) :
    p.selectInstance tc a = .selected i ↔ MostSpecialized tc (p.instancesOf tc) a i := by
  rw [Program.selectInstance, select_iff]
  exact ⟨Selects.mostSpecialized_of_selected, Selects.of_mostSpecialized⟩

/-- Lookup is ambiguous exactly when two partial specializations match and
neither is more specialized than all the others. -/
theorem coherence_ambiguous (p : Program) (tc : String) (a : Ty) (l : List Nat) :
    p.selectInstance tc a = .ambiguous l ↔
      l = matching (p.instancesOf tc) a ∧
      (∃ i j, i ≠ j ∧ Matches (p.instancesOf tc) a i ∧ Matches (p.instancesOf tc) a j) ∧
      ∀ i, ¬ MostSpecialized tc (p.instancesOf tc) a i := by
  rw [Program.selectInstance, select_iff]
  constructor
  · intro h
    cases h with
    | ambiguous htwo hnone => exact ⟨rfl, htwo, hnone⟩
  · rintro ⟨rfl, htwo, hnone⟩
    exact .ambiguous htwo hnone

/-- Lookup never makes the program ill-formed by itself; ambiguity is
reported as ambiguity. -/
theorem selectInstance_ne_illFormed (p : Program) (tc : String) (a : Ty) (r : Reason) :
    p.selectInstance tc a ≠ .illFormed r := by
  rw [Program.selectInstance, Ne, select_iff]
  intro h
  cases h

/-! ## Inserting a partial specialization -/

/-- Where position `i` of a list lands once an entry is inserted at `k`. -/
def shiftAt (k i : Nat) : Nat := if i < k then i else i + 1

theorem shiftAt_ne (k i : Nat) : shiftAt k i ≠ k := by
  unfold shiftAt
  split <;> omega

theorem shiftAt_inj {k i j : Nat} (h : shiftAt k i = shiftAt k j) : i = j := by
  unfold shiftAt at h
  split at h <;> split at h <;> omega

/-- Every position of the longer list is the inserted one or a shifted
old one. -/
theorem shiftAt_cases (k i' : Nat) : i' = k ∨ ∃ i, i' = shiftAt k i := by
  rcases Nat.lt_trichotomy i' k with h | h | h
  · exact .inr ⟨i', by simp [shiftAt, h]⟩
  · exact .inl h
  · exact .inr ⟨i' - 1, by unfold shiftAt; split <;> omega⟩

theorem getElem?_insert_shift {α : Type} (l₁ l₂ : List α) (n : α) (i : Nat) :
    (l₁ ++ n :: l₂)[shiftAt l₁.length i]? = (l₁ ++ l₂)[i]? := by
  unfold shiftAt
  split
  · next h => rw [List.getElem?_append_left h, List.getElem?_append_left h]
  · next h =>
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    have : i + 1 - l₁.length = (i - l₁.length) + 1 := by omega
    rw [this, List.getElem?_cons_succ]

section insert

variable (tc : String) (l₁ l₂ : List (Head × Ty)) (n : Head × Ty) (arg : Ty)

theorem matches_insert_shift (i : Nat) :
    Matches (l₁ ++ n :: l₂) arg (shiftAt l₁.length i) ↔ Matches (l₁ ++ l₂) arg i := by
  simp only [Matches, getElem?_insert_shift]

theorem matches_insert_at :
    Matches (l₁ ++ n :: l₂) arg l₁.length ↔ PatternMatches n.1 n.2 arg := by
  obtain ⟨h, pat⟩ := n
  simp only [Matches, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨_, _, ⟨rfl, rfl⟩, hm⟩
    exact hm
  · exact fun hm => ⟨h, pat, ⟨rfl, rfl⟩, hm⟩

theorem matchesAt_insert_shift (i : Nat) :
    matchesAt (l₁ ++ n :: l₂) arg (shiftAt l₁.length i) = matchesAt (l₁ ++ l₂) arg i := by
  simp only [matchesAt, getElem?_insert_shift]

theorem beats_insert_shift (i j : Nat) :
    beats tc (l₁ ++ n :: l₂) (shiftAt l₁.length i) (shiftAt l₁.length j) = beats tc (l₁ ++ l₂) i j := by
  simp only [beats, getElem?_insert_shift]

theorem mostSpecialized_insert_shift {i : Nat}
    (h : MostSpecialized tc (l₁ ++ n :: l₂) arg (shiftAt l₁.length i)) :
    MostSpecialized tc (l₁ ++ l₂) arg i := by
  refine ⟨(matches_insert_shift l₁ l₂ n arg i).1 h.1, fun j hj hne => ?_⟩
  rw [← beats_insert_shift tc l₁ l₂ n]
  exact h.2 _ ((matches_insert_shift l₁ l₂ n arg j).2 hj) fun e => hne (shiftAt_inj e)

/-- The matching positions, when the inserted entry does not match, are
the old ones shifted. -/
theorem matching_insert (hn : ¬ PatternMatches n.1 n.2 arg) :
    matching (l₁ ++ n :: l₂) arg = (matching (l₁ ++ l₂) arg).map (shiftAt l₁.length) := by
  have hk : matchesAt (l₁ ++ n :: l₂) arg l₁.length = false := by
    cases h : matchesAt (l₁ ++ n :: l₂) arg l₁.length
    · rfl
    · exact absurd ((matches_insert_at l₁ l₂ n arg).1 (matchesAt_iff.1 h)) hn
  have hlen' : (l₁ ++ n :: l₂).length = l₁.length + (l₂.length + 1) := by simp
  have hlen : (l₁ ++ l₂).length = l₁.length + l₂.length := by simp
  simp only [matching, hlen', hlen, List.range_add, List.range_succ_eq_map, List.filter_append,
    List.map_cons, List.filter_cons, List.map_append, List.filter_map, List.map_map]
  simp only [Nat.add_zero, hk, Bool.false_eq_true, ite_false]
  congr 1
  · -- Below the insertion point nothing moves.
    have hlo : ∀ i ∈ List.range l₁.length, shiftAt l₁.length i = i := fun i hi => by
      simp [shiftAt, List.mem_range.1 hi]
    rw [List.map_congr_left (fun i hi => hlo i (List.mem_filter.1 hi).1), List.map_id']
    apply List.filter_congr
    intro i hi
    rw [← hlo i hi, matchesAt_insert_shift, hlo i hi]
  · -- Above it every position moves up by one.
    have hhi : ∀ j, shiftAt l₁.length (l₁.length + j) = l₁.length + (j + 1) := fun j => by
      unfold shiftAt
      split <;> omega
    simp only [Function.comp_def, hhi]
    congr 1
    apply List.filter_congr
    intro j _
    rw [← hhi, matchesAt_insert_shift]

/-- Inserting an entry the argument does not match changes the selection
only by the shift of positions. -/
theorem select_insert_unmatched (hn : ¬ PatternMatches n.1 n.2 arg) :
    select tc (l₁ ++ n :: l₂) arg = (select tc (l₁ ++ l₂) arg).map (shiftAt l₁.length) := by
  rw [select_iff]
  have hs := select_sound tc (l₁ ++ l₂) arg
  generalize select tc (l₁ ++ l₂) arg = r at hs
  have hk : ¬ Matches (l₁ ++ n :: l₂) arg l₁.length := fun h =>
    hn ((matches_insert_at l₁ l₂ n arg).1 h)
  -- A most specialized old match stays the most specialized, shifted.
  have hms : ∀ i, MostSpecialized tc (l₁ ++ l₂) arg i →
      MostSpecialized tc (l₁ ++ n :: l₂) arg (shiftAt l₁.length i) := fun i h => by
    refine ⟨(matches_insert_shift l₁ l₂ n arg i).2 h.1, fun j' hj' hne => ?_⟩
    rcases shiftAt_cases l₁.length j' with rfl | ⟨j, rfl⟩
    · exact absurd hj' hk
    · rw [beats_insert_shift]
      exact h.2 j ((matches_insert_shift l₁ l₂ n arg j).1 hj') fun e => hne (e ▸ rfl)
  cases hs with
  | unique i hm hu =>
    exact .of_mostSpecialized (hms i ⟨hm, fun j hj hne => absurd (hu j hj) hne⟩)
  | mostSpecialized i _ h => exact .of_mostSpecialized (hms i h)
  | ambiguous htwo hnone =>
    simp only [Resolution.map]
    rw [← matching_insert l₁ l₂ n arg hn]
    refine .ambiguous ?_ fun i' h => ?_
    · obtain ⟨i, j, hne, hi, hj⟩ := htwo
      exact ⟨_, _, fun e => hne (shiftAt_inj e), (matches_insert_shift l₁ l₂ n arg i).2 hi,
        (matches_insert_shift l₁ l₂ n arg j).2 hj⟩
    · rcases shiftAt_cases l₁.length i' with rfl | ⟨i, rfl⟩
      · exact hk h.1
      · exact hnone i (mostSpecialized_insert_shift tc l₁ l₂ n arg h)
  | primary hno =>
    refine .primary fun i' h => ?_
    rcases shiftAt_cases l₁.length i' with rfl | ⟨i, rfl⟩
    · exact hk h
    · exact hno i ((matches_insert_shift l₁ l₂ n arg i).1 h)

/-- Inserting an entry the argument matches either leaves the selection
as it was, up to the shift of positions, or moves it to the new entry or
to ambiguity. -/
theorem select_insert_matched :
    select tc (l₁ ++ n :: l₂) arg = (select tc (l₁ ++ l₂) arg).map (shiftAt l₁.length) ∨
    select tc (l₁ ++ n :: l₂) arg = .selected l₁.length ∨
    ∃ l, select tc (l₁ ++ n :: l₂) arg = .ambiguous l := by
  have hs := select_sound tc (l₁ ++ n :: l₂) arg
  generalize hr : select tc (l₁ ++ n :: l₂) arg = r at hs
  cases r with
  | selected i' =>
    rcases shiftAt_cases l₁.length i' with rfl | ⟨i, rfl⟩
    · exact .inr (.inl rfl)
    · refine .inl ?_
      have h := mostSpecialized_insert_shift tc l₁ l₂ n arg hs.mostSpecialized_of_selected
      rw [(select_iff _ _ _ _).2 (Selects.of_mostSpecialized h)]
      rfl
  | ambiguous l => exact .inr (.inr ⟨l, rfl⟩)
  | noMatch =>
    refine .inl ?_
    cases hs with
    | primary hno =>
      have hk : ¬ PatternMatches n.1 n.2 arg := fun h =>
        hno l₁.length ((matches_insert_at l₁ l₂ n arg).2 h)
      rw [← hr, select_insert_unmatched tc l₁ l₂ n arg hk]
  | illFormed _ => cases hs

end insert

/-! ## Stability -/

/-- Stability: declaring a partial specialization of `tc` anywhere in a
program changes lookup of `tc` only at types the new one matches, and
there only to the new specialization or to ambiguity. A lookup that keeps
its answer keeps it up to the shift of positions past the insertion
point. -/
theorem stability (p₁ p₂ : Program) (tc : String) (h : Head) (pat : Ty) (a : Ty) :
    let p := p₁ ++ p₂
    let p' := p₁ ++ .instance tc h pat :: p₂
    let k := (p₁.instancesOf tc).length
    p'.selectInstance tc a = (p.selectInstance tc a).map (shiftAt k) ∨
    (PatternMatches h pat a ∧
      (p'.selectInstance tc a = .selected k ∨ ∃ l, p'.selectInstance tc a = .ambiguous l)) := by
  intro p p' k
  simp only [p, p', k, Program.selectInstance]
  rw [Program.instancesOf_insert, Program.instancesOf_append]
  by_cases hn : PatternMatches h pat a
  · rcases select_insert_matched tc (p₁.instancesOf tc) (p₂.instancesOf tc) (h, pat) a with e | e | e
    · exact .inl e
    · exact .inr ⟨hn, .inl e⟩
    · exact .inr ⟨hn, .inr e⟩
  · exact .inl (select_insert_unmatched tc _ _ (h, pat) a hn)

/-- Declaring a partial specialization of one variable template does not
move lookup of another. -/
theorem stability_other_typeclass (p₁ p₂ : Program) (tc tc' : String) (h : Head) (pat : Ty)
    (a : Ty) (hne : tc ≠ tc') :
    (p₁ ++ .instance tc h pat :: p₂).selectInstance tc' a = (p₁ ++ p₂).selectInstance tc' a := by
  simp only [Program.selectInstance, Program.instancesOf_insert_other _ _ _ _ _ _ hne]

end Overload
