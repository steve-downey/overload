-- Overload/Transitivity.lean                                         -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Generality
import Overload.Ordering

/-!
# More specialized is transitive

The proof target that phase 4 left open. It comes in two layers.

1. More specialized is transitive whenever at least as specialized is,
   on the three templates involved (`moreSpecialized_trans_of`). The
   gate of [temp.func.order]/8 and more-constrained are transitive
   outright (`tieBreakApplies_trans`, `moreConstrained_trans`), and the
   mixed cases go through the asymmetry of the deduction order.
2. At least as specialized is transitive on templates whose parameters
   are types and whose parameter types are first-order
   (`atLeastAsSpecialized_trans`). Deduction there is matching, and a
   match against the synthesized types of a template lifts to every
   substitution of that template.

References are outside the second layer. The tie-breaks of
[temp.deduct.partial]/9 then enter, and the bounded search in
`OverloadTest/Ordering.lean` is what covers them.
-/

namespace Overload

namespace PartialOrdering

theorem paramEquivalent_trans {p q r : TemplateParam} (h₁ : paramEquivalent p q = true)
    (h₂ : paramEquivalent q r = true) : paramEquivalent p r = true := by
  unfold paramEquivalent at *
  cases hp : p.kind <;> cases hq : q.kind <;> cases hr : r.kind <;> simp_all

theorem headsEquivalent_trans {h₁ h₂ h₃ : Head} (e₁ : headsEquivalent h₁ h₂ = true)
    (e₂ : headsEquivalent h₂ h₃ = true) : headsEquivalent h₁ h₃ = true := by
  induction h₁ generalizing h₂ h₃ with
  | nil =>
    cases h₂ with
    | nil => exact e₂
    | cons _ _ => simp [headsEquivalent] at e₁
  | cons p ps ih =>
    cases h₂ with
    | nil => simp [headsEquivalent] at e₁
    | cons q qs =>
      cases h₃ with
      | nil => simp [headsEquivalent] at e₂
      | cons r rs =>
        simp only [headsEquivalent, List.length_cons, List.zip_cons_cons, List.all_cons,
          Bool.and_eq_true, beq_iff_eq, Nat.add_right_cancel_iff] at e₁ e₂ ⊢
        obtain ⟨hl₁, hp₁, ht₁⟩ := e₁
        obtain ⟨hl₂, hp₂, ht₂⟩ := e₂
        have := ih (h₂ := qs) (h₃ := rs) (by simp [headsEquivalent, hl₁, ht₁])
          (by simp [headsEquivalent, hl₂, ht₂])
        simp only [headsEquivalent, Bool.and_eq_true, beq_iff_eq] at this
        exact ⟨hl₁.trans hl₂, paramEquivalent_trans hp₁ hp₂, this.2⟩

/-- The gate of [temp.func.order]/8 is transitive. -/
theorem tieBreakApplies_trans {f g h : FunctionTemplate} (h₁ : tieBreakApplies f g = true)
    (h₂ : tieBreakApplies g h = true) : tieBreakApplies f h = true := by
  simp only [tieBreakApplies, Bool.and_eq_true, beq_iff_eq] at *
  obtain ⟨⟨⟨a₁, b₁⟩, c₁⟩, d₁⟩ := h₁
  obtain ⟨⟨⟨a₂, b₂⟩, c₂⟩, d₂⟩ := h₂
  exact ⟨⟨⟨a₁.trans a₂, b₁.trans b₂⟩, headsEquivalent_trans c₁ c₂⟩, d₁.trans d₂⟩

end PartialOrdering

/-- More constrained is transitive: the strict part of a preorder. -/
theorem Constraint.moreConstrained_trans {c₁ c₂ c₃ : Option Constraint}
    (h₁ : Constraint.moreConstrained c₁ c₂ = true) (h₂ : Constraint.moreConstrained c₂ c₃ = true) :
    Constraint.moreConstrained c₁ c₃ = true := by
  simp only [Constraint.moreConstrained, Bool.and_eq_true, Bool.not_eq_true'] at *
  refine ⟨Constraint.atLeastAsConstrained_trans h₁.1 h₂.1, ?_⟩
  cases h : Constraint.atLeastAsConstrained c₃ c₁ with
  | false => rfl
  | true =>
    have := Constraint.atLeastAsConstrained_trans h h₁.1
    rw [h₂.2] at this
    cases this

namespace PartialOrdering

/-- More specialized is transitive on three templates on which at least as
specialized is. -/
theorem moreSpecialized_trans_of (ctx : Option Nat) (f g h : FunctionTemplate)
    (hT : ∀ x ∈ [f, g, h], ∀ y ∈ [f, g, h], ∀ z ∈ [f, g, h],
      atLeastAsSpecialized x y ctx = true → atLeastAsSpecialized y z ctx = true →
        atLeastAsSpecialized x z ctx = true)
    (h₁ : moreSpecialized ctx f g = true) (h₂ : moreSpecialized ctx g h = true) :
    moreSpecialized ctx f h = true := by
  have mf : f ∈ [f, g, h] := by simp
  have mg : g ∈ [f, g, h] := by simp
  have mh : h ∈ [f, g, h] := by simp
  simp only [moreSpecialized, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h₁ h₂ ⊢
  rcases h₁ with ⟨fg, gf⟩ | ⟨⟨⟨fg, gf⟩, tfg⟩, cfg⟩ <;>
    rcases h₂ with ⟨gh, hg⟩ | ⟨⟨⟨gh, hg⟩, tgh⟩, cgh⟩
  · -- both by deduction
    left
    refine ⟨hT f mf g mg h mh fg gh, ?_⟩
    cases hf : atLeastAsSpecialized h f ctx with
    | false => rfl
    | true => rw [hT g mg h mh f mf gh hf] at gf; cases gf
  · -- by deduction, then by constraints
    left
    refine ⟨hT f mf g mg h mh fg gh, ?_⟩
    cases hf : atLeastAsSpecialized h f ctx with
    | false => rfl
    | true => rw [hT g mg h mh f mf gh hf] at gf; cases gf
  · -- by constraints, then by deduction
    left
    refine ⟨hT f mf g mg h mh fg gh, ?_⟩
    cases hf : atLeastAsSpecialized h f ctx with
    | false => rfl
    | true => rw [hT h mh f mf g mg hf fg] at hg; cases hg
  · -- both by constraints
    right
    exact ⟨⟨⟨hT f mf g mg h mh fg gh, hT h mh g mg f mf hg gf⟩, tieBreakApplies_trans tfg tgh⟩,
      Constraint.moreConstrained_trans cfg cgh⟩

end PartialOrdering

/-! ## Undoing the synthesized types -/

/-- Replace each synthesized type by what `θ` binds its parameter to. -/
def Ty.unsynth (θ : Bindings) : Ty → Ty
  | .synth i => (θ.lookup i).getD (.synth i)
  | .named n => .named n
  | .param i => .param i
  | .const t => .const (Ty.unsynth θ t)
  | .ptr t => .ptr (Ty.unsynth θ t)
  | .lref t => .lref (Ty.unsynth θ t)
  | .rref t => .rref (Ty.unsynth θ t)
  | .spec c as => .spec c (Ty.unsynth θ as)
  | .nil => .nil
  | .cons a as => .cons (Ty.unsynth θ a) (Ty.unsynth θ as)
  | .value v => .value v
  | .nondeduced t => .nondeduced (Ty.unsynth θ t)
  | .lookup n a => .lookup n (Ty.unsynth θ a)
  | .ref t => .ref (Ty.unsynth θ t)
  | .removeCvref t => .removeCvref (Ty.unsynth θ t)
  | .typeOf t => .typeOf (Ty.unsynth θ t)
  | .enableIf c as t => .enableIf c (Ty.unsynth θ as) (Ty.unsynth θ t)
  | .fn ps r => .fn (Ty.unsynth θ ps) (Ty.unsynth θ r)

/-- A parameter type of the fragment: first-order, with no reference, no
constant argument that mentions a parameter, and no synthesized type. -/
def Ty.plain : Ty → Bool
  | .named _ | .nil | .param _ => true
  | .const t | .ptr t => Ty.plain t
  | .spec _ as => Ty.plain as
  | .cons a as => Ty.plain a && Ty.plain as
  | .value v => !v.dependent
  | _ => false

theorem Ty.plain_firstOrder : ∀ t : Ty, t.plain = true → t.firstOrder = true
  | .named _, _ | .nil, _ | .param _, _ => rfl
  | .const t, h | .ptr t, h => Ty.plain_firstOrder t h
  | .spec _ as, h => Ty.plain_firstOrder as h
  | .cons a as, h => by
    simp only [Ty.plain, Bool.and_eq_true] at h
    simp [Ty.firstOrder, Ty.plain_firstOrder a h.1, Ty.plain_firstOrder as h.2]
  | .value v, h => by
    simp only [Ty.plain, Bool.not_eq_true'] at h
    cases v <;> simp_all [Ty.firstOrder, Val.firstOrder]

/-- Bindings whose arguments are all types. -/
def Bindings.Types (θ : Bindings) : Prop := ∀ i x, θ.lookup i = some x → x.isType = true

theorem Bindings.Types.kinded {θ : Bindings} (h : θ.Types) : θ.Kinded :=
  fun i x hx => .inl (h i x hx)

theorem Ty.isType_unsynth {θ : Bindings} (hθ : θ.Types) (x : Ty) :
    (Ty.unsynth θ x).isType = x.isType := by
  cases x with
  | synth i =>
    simp only [Ty.unsynth]
    cases h : θ.lookup i with
    | none => rfl
    | some y => simpa [Ty.isType] using hθ i y h
  | _ => rfl

/-- The bindings `σ` with each argument unsynthesized. -/
def Bindings.unsynth (σ θ : Bindings) : Bindings := σ.map fun (i, x) => (i, Ty.unsynth θ x)

theorem Bindings.lookup_unsynth (θ σ : Bindings) (i : ParamIdx) :
    (σ.unsynth θ).lookup i = (σ.lookup i).map (Ty.unsynth θ) := by
  induction σ with
  | nil => rfl
  | cons b σ ih =>
    obtain ⟨j, x⟩ := b
    by_cases hji : j = i
    · subst hji; simp [Bindings.unsynth, Bindings.lookup]
    · simp only [Bindings.unsynth, List.map_cons] at ih ⊢
      simp only [Bindings.lookup, List.find?_cons, hji, decide_false] at ih ⊢
      exact ih

/-- Unsynthesizing after substituting is substituting the unsynthesized
bindings, for a plain type. -/
theorem Ty.unsynth_subst {θ : Bindings} (hθ : θ.Types) (σ : Bindings) :
    ∀ t : Ty, t.plain = true → Ty.unsynth θ (Ty.subst σ t) = Ty.subst (σ.unsynth θ) t
  | .named _, _ | .nil, _ => rfl
  | .param i, _ => by
    simp only [Ty.subst, Bindings.lookup_unsynth]
    cases h : σ.lookup i with
    | none => rfl
    | some x =>
      cases x with
      | ref r => rfl
      | synth j =>
        simp only [Option.map_some, Ty.isType, ↓reduceIte, Ty.unsynth]
        cases hj : θ.lookup j with
        | none => rfl
        | some y =>
          have hy := hθ j y hj
          cases y <;> simp_all [Ty.isType]
      | _ => simp [Ty.isType, Ty.unsynth]
  | .const t, h => by simp only [Ty.subst, Ty.unsynth, Ty.unsynth_subst hθ σ t h]
  | .ptr t, h => by simp only [Ty.subst, Ty.unsynth, Ty.unsynth_subst hθ σ t h]
  | .spec c as, h => by simp only [Ty.subst, Ty.unsynth, Ty.unsynth_subst hθ σ as h]
  | .cons a as, h => by
    simp only [Ty.plain, Bool.and_eq_true] at h
    simp only [Ty.subst, Ty.unsynth, Ty.unsynth_subst hθ σ a h.1, Ty.unsynth_subst hθ σ as h.2]
  | .value v, h => by
    simp only [Ty.plain, Bool.not_eq_true'] at h
    simp only [Ty.subst, Ty.unsynth, Val.subst_of_not_dependent _ v h]

namespace PartialOrdering

private theorem synth_lookup_go (F : TemplateParam × Nat → ParamIdx × Ty)
    (hF : ∀ p n, p.kind = .type → F (p, n) = (n, synthType n)) :
    ∀ (h : Head) (n i : Nat), (∀ p ∈ h, p.kind = .type) → n ≤ i → i < n + h.length →
      Bindings.lookup ((h.zipIdx n).map F) i = some (synthType i) := by
  intro h
  induction h with
  | nil => intro n i _ _ hi; simp at hi; omega
  | cons p ps ih =>
    intro n i hk hn hi
    rw [List.zipIdx_cons, List.map_cons, hF p n (hk p List.mem_cons_self)]
    by_cases hin : i = n
    · subst hin; exact lookup_cons_self _ _ _
    · rw [lookup_cons_other _ _ hin]
      exact ih (n + 1) i (fun q hq => hk q (List.mem_cons_of_mem _ hq)) (by omega)
        (by simp at hi; omega)

/-- The synthesized bindings of a head of type parameters. -/
theorem synthBindings_lookup (h : Head) (hk : ∀ p ∈ h, p.kind = .type) (i : ParamIdx)
    (hi : i < h.length) : (synthBindings h).lookup i = some (synthType i) := by
  unfold synthBindings
  have hi' : i < 0 + h.length := by rw [Nat.zero_add]; exact hi
  refine synth_lookup_go _ ?_ h 0 i hk (Nat.zero_le _) hi'
  intro p n hp
  simp [hp]

/-- Unsynthesizing a template's synthesized types gives back any
substitution that binds its parameters to types. -/
theorem unsynth_subst_synth (h : Head) (hk : ∀ p ∈ h, p.kind = .type) {θ : Bindings}
    (hθ : θ.Types) : ∀ t : Ty, t.plain = true →
      (∀ i ∈ usedParams t, i < h.length ∧ (θ.lookup i).isSome) →
      Ty.unsynth θ (Ty.subst (synthBindings h) t) = Ty.subst θ t
  | .named _, _, _ | .nil, _, _ => rfl
  | .param i, _, hu => by
    obtain ⟨hi, hs⟩ := hu i (by simp [usedParams])
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
    have hxt := hθ i x hx
    simp only [Ty.subst, synthBindings_lookup h hk i hi, synthType, Ty.isType, ↓reduceIte,
      Ty.unsynth, hx, Option.getD_some]
    cases x <;> simp_all [Ty.isType]
  | .const t, hp, hu => by
    simp only [Ty.subst, Ty.unsynth, unsynth_subst_synth h hk hθ t hp (by simpa [usedParams] using hu)]
  | .ptr t, hp, hu => by
    simp only [Ty.subst, Ty.unsynth, unsynth_subst_synth h hk hθ t hp (by simpa [usedParams] using hu)]
  | .spec c as, hp, hu => by
    simp only [Ty.subst, Ty.unsynth, unsynth_subst_synth h hk hθ as hp (by simpa [usedParams] using hu)]
  | .cons a as, hp, hu => by
    simp only [Ty.plain, Bool.and_eq_true] at hp
    simp only [usedParams, List.mem_append] at hu
    simp only [Ty.subst, Ty.unsynth, unsynth_subst_synth h hk hθ a hp.1 (fun i hi => hu i (.inl hi)),
      unsynth_subst_synth h hk hθ as hp.2 (fun i hi => hu i (.inr hi))]
  | .value v, hp, _ => by
    simp only [Ty.plain, Bool.not_eq_true'] at hp
    simp only [Ty.subst, Ty.unsynth, Val.subst_of_not_dependent _ v hp]

/-! ## Deduction on plain pairs -/

theorem usedVal_of_not_dependent : ∀ v : Val, v.dependent = false → usedParams.usedVal v = []
  | .int _, _ | .bool _, _ | .nil, _ => rfl
  | .obj _ vs, h => by simp only [Val.dependent] at h; simp [usedParams.usedVal, usedVal_of_not_dependent vs h]
  | .cons v vs, h => by
    simp only [Val.dependent, Bool.or_eq_false_iff] at h
    simp [usedParams.usedVal, usedVal_of_not_dependent v h.1, usedVal_of_not_dependent vs h.2]
  | .param _, h => by simp [Val.dependent] at h

/-- Deduction binds every parameter a plain `P` uses. -/
theorem deduceTy_binds : ∀ (p : Ty), p.plain = true → ∀ (a : Ty) (σ σ' : Bindings),
    deduceTy p a σ = some σ' → ∀ i ∈ usedParams p, (σ'.lookup i).isSome
  | .param j, _, a, σ, σ', h, i, hi => by
    simp only [usedParams, List.mem_singleton] at hi
    subst hi
    simp only [deduceTy] at h
    split at h
    · simp [(bindArg_spec h).1]
    · cases h
  | .value v, hp, _, _, _, _, i, hi => by
    simp only [Ty.plain, Bool.not_eq_true'] at hp
    simp [usedParams, usedVal_of_not_dependent v hp] at hi
  | .named _, _, _, _, _, _, i, hi | .nil, _, _, _, _, _, i, hi => by simp [usedParams] at hi
  | .const p, hp, a, σ, σ', h, i, hi => by
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    exact deduceTy_binds p hp _ σ σ' h i (by simpa [usedParams] using hi)
  | .ptr p, hp, a, σ, σ', h, i, hi => by
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    exact deduceTy_binds p hp _ σ σ' h i (by simpa [usedParams] using hi)
  | .spec c ps, hp, a, σ, σ', h, i, hi => by
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    split at h
    · exact deduceTy_binds ps hp _ σ σ' h i (by simpa [usedParams] using hi)
    · cases h
  | .cons p ps, hp, a, σ, σ', h, i, hi => by
    simp only [Ty.plain, Bool.and_eq_true] at hp
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    rename_i a as
    cases h₁ : deduceTy p a σ with
    | none => rw [h₁] at h; cases h
    | some σ₁ =>
      rw [h₁] at h
      simp only [usedParams, List.mem_append] at hi
      rcases hi with hi | hi
      · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (deduceTy_binds p hp.1 a σ σ₁ h₁ i hi)
        simp [deduceTy_sub ps as σ₁ σ' h i x hx]
      · exact deduceTy_binds ps hp.2 as σ₁ σ' h i hi

/-- Deduction on a plain `P` binds parameters only to types. -/
theorem deduceTy_types : ∀ (p : Ty), p.plain = true → ∀ (a : Ty) (σ σ' : Bindings), σ.Types →
    deduceTy p a σ = some σ' → σ'.Types
  | .param j, _, a, σ, σ', hσ, h => by
    simp only [deduceTy] at h
    split at h
    · rename_i ha
      unfold bindArg at h
      split at h
      · split at h
        · simp only [Option.some.injEq] at h; subst h; exact hσ
        · cases h
      · simp only [Option.some.injEq] at h
        subst h
        intro i x hx
        by_cases hij : i = j
        · subst hij; rw [lookup_cons_self] at hx; cases hx; exact ha
        · rw [lookup_cons_other _ _ hij] at hx; exact hσ i x hx
    · cases h
  | .value v, hp, a, σ, σ', hσ, h => by
    simp only [Ty.plain, Bool.not_eq_true'] at hp
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    unfold deduceVal at h
    split at h
    · simp [Val.dependent] at hp
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; exact hσ
      · cases h
  | .named _, _, a, σ, σ', hσ, h => by
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact hσ
    · cases h
  | .nil, _, a, σ, σ', hσ, h => by
    cases a <;> simp only [deduceTy, reduceCtorEq, Option.some.injEq] at h
    subst h; exact hσ
  | .const p, hp, a, σ, σ', hσ, h => by
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    exact deduceTy_types p hp _ σ σ' hσ h
  | .ptr p, hp, a, σ, σ', hσ, h => by
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    exact deduceTy_types p hp _ σ σ' hσ h
  | .spec c ps, hp, a, σ, σ', hσ, h => by
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    split at h
    · exact deduceTy_types ps hp _ σ σ' hσ h
    · cases h
  | .cons p ps, hp, a, σ, σ', hσ, h => by
    simp only [Ty.plain, Bool.and_eq_true] at hp
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    rename_i a as
    cases h₁ : deduceTy p a σ with
    | none => rw [h₁] at h; cases h
    | some σ₁ =>
      rw [h₁] at h
      exact deduceTy_types ps hp.2 as σ₁ σ' (deduceTy_types p hp.1 a σ σ₁ hσ h₁) h

theorem Ty.plain_stripConst (t : Ty) (h : t.plain = true) : t.stripConst.plain = true := by
  cases t <;> simp_all [Ty.stripConst, Ty.plain]

theorem Ty.plain_isRef (t : Ty) (h : t.plain = true) : t.isRef = false := by
  cases t <;> simp_all [Ty.isRef, Ty.plain]

theorem usedParams_stripConst (t : Ty) : usedParams t.stripConst = usedParams t := by
  cases t <;> rfl

/-- Partial ordering's pair deduction, on a plain `P` against a type that
is not a reference: deduction of the types with top-level `const`
removed, and never a denial. -/
theorem deducePair_plain (p a : Ty) (σ : Bindings) (hp : p.plain = true) (ha : a.isRef = false) :
    deducePair p a σ = (deduceTy p.stripConst a.stripConst σ, false) := by
  have hpr : p.isRef = false := Ty.plain_isRef p hp
  have e₁ : p.referred = p := by cases p <;> simp_all [Ty.referred, Ty.isRef]
  have e₂ : a.referred = a := by cases a <;> simp_all [Ty.referred, Ty.isRef]
  unfold deducePair
  simp only [hpr, ha, e₁, e₂, Bool.false_and, Bool.and_false]
  cases deduceTy p.stripConst a.stripConst σ <;> rfl

theorem denies_plain (p a : Ty) (hp : p.plain = true) : denies p a = false := by
  unfold denies deducePair
  simp only [Ty.plain_isRef p hp, Bool.false_and, Bool.and_false]
  split <;> rfl

/-! ## The chain of pairs -/

/-- Pairs whose `P` is plain and whose `A` is not a reference. -/
def PlainPairs (pairs : List (Ty × Ty)) : Prop := ∀ x ∈ pairs, x.1.plain = true ∧ x.2.isRef = false

theorem go_sound : ∀ (pairs : List (Ty × Ty)) (σ σ' : Bindings), PlainPairs pairs →
    deduceAll.go pairs σ = some σ' →
      σ.Sub σ' ∧ ∀ x ∈ pairs, ∀ τ, σ'.Sub τ → Ty.subst τ x.1.stripConst = x.2.stripConst
  | [], σ, σ', _, h => by
    simp only [deduceAll.go, Option.some.injEq] at h; subst h
    exact ⟨Bindings.Sub.refl _, fun x hx => by cases hx⟩
  | (p, a) :: rest, σ, σ', hp, h => by
    have ⟨hpp, har⟩ := hp (p, a) List.mem_cons_self
    simp only [deduceAll.go, deducePair_plain p a σ hpp har] at h
    cases h₁ : deduceTy p.stripConst a.stripConst σ with
    | none => rw [h₁] at h; cases h
    | some σ₁ =>
      rw [h₁] at h
      obtain ⟨hs, hrest⟩ := go_sound rest σ₁ σ' (fun x hx => hp x (List.mem_cons_of_mem _ hx)) h
      refine ⟨(deduceTy_sub _ _ σ σ₁ h₁).trans hs, ?_⟩
      intro x hx τ hτ
      rcases List.mem_cons.mp hx with rfl | hx
      · exact deduceTy_subst_ext _ (Ty.plain_firstOrder _ (Ty.plain_stripConst p hpp)) _ σ σ₁ h₁ τ
          (hs.trans hτ)
      · exact hrest x hx τ hτ

theorem go_types : ∀ (pairs : List (Ty × Ty)) (σ σ' : Bindings), PlainPairs pairs → σ.Types →
    deduceAll.go pairs σ = some σ' → σ'.Types
  | [], σ, σ', _, hσ, h => by simp only [deduceAll.go, Option.some.injEq] at h; subst h; exact hσ
  | (p, a) :: rest, σ, σ', hp, hσ, h => by
    have ⟨hpp, har⟩ := hp (p, a) List.mem_cons_self
    simp only [deduceAll.go, deducePair_plain p a σ hpp har] at h
    cases h₁ : deduceTy p.stripConst a.stripConst σ with
    | none => rw [h₁] at h; cases h
    | some σ₁ =>
      rw [h₁] at h
      exact go_types rest σ₁ σ' (fun x hx => hp x (List.mem_cons_of_mem _ hx))
        (deduceTy_types _ (Ty.plain_stripConst p hpp) _ σ σ₁ hσ h₁) h

theorem go_binds : ∀ (pairs : List (Ty × Ty)) (σ σ' : Bindings), PlainPairs pairs →
    deduceAll.go pairs σ = some σ' → ∀ x ∈ pairs, ∀ i ∈ usedParams x.1, (σ'.lookup i).isSome
  | [], _, _, _, _ => fun x hx => by cases hx
  | (p, a) :: rest, σ, σ', hp, h => by
    have ⟨hpp, har⟩ := hp (p, a) List.mem_cons_self
    simp only [deduceAll.go, deducePair_plain p a σ hpp har] at h
    cases h₁ : deduceTy p.stripConst a.stripConst σ with
    | none => rw [h₁] at h; cases h
    | some σ₁ =>
      rw [h₁] at h
      have hp' : PlainPairs rest := fun x hx => hp x (List.mem_cons_of_mem _ hx)
      intro x hx i hi
      rcases List.mem_cons.mp hx with rfl | hx
      · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp
          (deduceTy_binds _ (Ty.plain_stripConst p hpp) _ σ σ₁ h₁ i (by rwa [usedParams_stripConst]))
        simp [(go_sound rest σ₁ σ' hp' h).1 i y hy]
      · exact go_binds rest σ₁ σ' hp' h x hx i hi

theorem go_complete (τ : Bindings) (hτ : τ.Kinded) : ∀ (pairs : List (Ty × Ty)) (σ : Bindings),
    PlainPairs pairs →
    (∀ x ∈ pairs, Ty.subst τ x.1.stripConst = x.2.stripConst ∧ x.2.stripConst.dependent = false) →
    σ.Sub τ → ∃ σ', deduceAll.go pairs σ = some σ' ∧ σ'.Sub τ
  | [], σ, _, _, hσ => ⟨σ, rfl, hσ⟩
  | (p, a) :: rest, σ, hp, hs, hσ => by
    have ⟨hpp, har⟩ := hp (p, a) List.mem_cons_self
    have ⟨e, hd⟩ := hs (p, a) List.mem_cons_self
    obtain ⟨σ₁, h₁, hsub₁⟩ := deduceTy_most_general _ (Ty.plain_firstOrder _ (Ty.plain_stripConst p hpp))
      _ σ τ hτ hσ e hd
    obtain ⟨σ', h₂, hsub⟩ := go_complete τ hτ rest σ₁ (fun x hx => hp x (List.mem_cons_of_mem _ hx))
      (fun x hx => hs x (List.mem_cons_of_mem _ hx)) hsub₁
    refine ⟨σ', ?_, hsub⟩
    simp only [deduceAll.go, deducePair_plain p a σ hpp har, h₁, h₂]

/-! ## Transitivity on the fragment -/

/-- A template of the fragment: type parameters only, plain parameter
types, and every parameter a type uses in scope. -/
structure Simple (ft : FunctionTemplate) : Prop where
  types : ∀ p ∈ ft.head, p.kind = .type
  plain : ∀ t ∈ ft.params, t.plain = true
  inScope : ∀ t ∈ ft.params, ∀ i ∈ usedParams t, i < ft.head.length

theorem mem_nominated {ft : FunctionTemplate} {ctx : Option Nat} {t : Ty}
    (h : t ∈ nominated ft ctx) : t ∈ ft.params := by
  cases ctx with
  | none => exact h
  | some m => exact List.mem_of_mem_take h

/-- A plain type in scope, with the synthesized types substituted: not a
reference, `const` only where it was, and ground. -/
theorem subst_synth_props (h : Head) (hk : ∀ p ∈ h, p.kind = .type) :
    ∀ t : Ty, t.plain = true → (∀ i ∈ usedParams t, i < h.length) →
      (Ty.subst (synthBindings h) t).dependent = false
  | .param i, _, hs => by
    simp [Ty.subst, synthBindings_lookup h hk i (hs i (by simp [usedParams])), synthType, Ty.isType,
      Ty.dependent]
  | .named _, _, _ | .nil, _, _ => rfl
  | .const t, hp, hs | .ptr t, hp, hs => by
    simpa [Ty.subst, Ty.dependent] using subst_synth_props h hk t hp (by simpa [usedParams] using hs)
  | .spec c as, hp, hs => by
    simpa [Ty.subst, Ty.dependent] using subst_synth_props h hk as hp (by simpa [usedParams] using hs)
  | .cons a as, hp, hs => by
    simp only [Ty.plain, Bool.and_eq_true] at hp
    simp only [usedParams, List.mem_append] at hs
    simp [Ty.subst, Ty.dependent, subst_synth_props h hk a hp.1 (fun i hi => hs i (.inl hi)),
      subst_synth_props h hk as hp.2 (fun i hi => hs i (.inr hi))]
  | .value v, hp, _ => by
    simp only [Ty.plain, Bool.not_eq_true'] at hp
    simp [Ty.subst, Val.subst_of_not_dependent _ v hp, Ty.dependent, hp]

theorem subst_synth_isRef (h : Head) (hk : ∀ p ∈ h, p.kind = .type) (t : Ty) (hp : t.plain = true)
    (hs : ∀ i ∈ usedParams t, i < h.length) : (Ty.subst (synthBindings h) t).isRef = false := by
  cases t with
  | param i => simp [Ty.subst, synthBindings_lookup h hk i (hs i (by simp [usedParams])), synthType,
      Ty.isType, Ty.isRef]
  | _ => simp_all [Ty.subst, Ty.isRef, Ty.plain]

theorem subst_synth_stripConst (h : Head) (hk : ∀ p ∈ h, p.kind = .type) (t : Ty)
    (hp : t.plain = true) (hs : ∀ i ∈ usedParams t, i < h.length) :
    (Ty.subst (synthBindings h) t).stripConst = Ty.subst (synthBindings h) t.stripConst := by
  cases t with
  | param i => simp [Ty.subst, synthBindings_lookup h hk i (hs i (by simp [usedParams])), synthType,
      Ty.isType, Ty.stripConst]
  | _ => simp_all [Ty.plain, Ty.subst, Ty.stripConst]

private theorem mem_zip_left {ps : List Ty} {as : List Ty} (hl : ps.length = as.length) :
    ∀ p ∈ ps, ∃ a, (p, a) ∈ ps.zip as := by
  induction ps generalizing as with
  | nil => intro p hp; cases hp
  | cons q qs ih =>
    cases as with
    | nil => simp at hl
    | cons b bs =>
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨b, by simp⟩
      · obtain ⟨a, ha⟩ := ih (by simpa using hl) p hp
        exact ⟨a, by simp [ha]⟩

/-- At least as specialized, on the fragment: deduction of the other
template's nominated types from the transformed ones, with no denial. -/
theorem atLeast_simple (ctx : Option Nat) (f g : FunctionTemplate) (hf : Simple f) :
    atLeastAsSpecialized f g ctx =
      deduceAll (nominated g ctx) (transform f.head (nominated f ctx)) := by
  unfold atLeastAsSpecialized direction
  have : ((nominated f ctx).zip (transform g.head (nominated g ctx))).any (fun (p, a) => denies p a) =
      false := by
    rw [List.any_eq_false]
    intro x hx
    obtain ⟨p, a⟩ := x
    have := denies_plain p a (hf.plain p (mem_nominated (List.of_mem_zip hx).1))
    simp [this]
  simp [this]

/-- The composition step: a match of `h` against `g`'s synthesized types,
unsynthesized with `g`'s match against `f`, is a match of `h` against
`f`'s. -/
theorem compose_matches (g : FunctionTemplate) (hg : Simple g) (Sf : Bindings) (σ₁ σ₂ : Bindings)
    (h₁ : σ₁.Types) :
    ∀ (Ph Pg Pf : List Ty), Ph.length = Pg.length → Pg.length = Pf.length →
      (∀ t ∈ Ph, t.plain = true) → (∀ t ∈ Pg, t ∈ g.params) →
      (∀ t ∈ Pg, ∀ i ∈ usedParams t, (σ₁.lookup i).isSome) →
      (∀ x ∈ Pg.zip (Pf.map (Ty.subst Sf)), Ty.subst σ₁ x.1.stripConst = x.2.stripConst) →
      (∀ x ∈ Ph.zip (Pg.map (Ty.subst (synthBindings g.head))),
        Ty.subst σ₂ x.1.stripConst = x.2.stripConst) →
      ∀ x ∈ Ph.zip (Pf.map (Ty.subst Sf)), Ty.subst (σ₂.unsynth σ₁) x.1.stripConst = x.2.stripConst
  | [], _, _, _, _, _, _, _, _, _ => fun x hx => by cases hx
  | ph :: Ph, [], _, hl, _, _, _, _, _, _ => by simp at hl
  | ph :: Ph, pg :: Pg, [], _, hl, _, _, _, _, _ => by simp at hl
  | ph :: Ph, pg :: Pg, pf :: Pf, hl₁, hl₂, hph, hpg, hb, hm₁, hm₂ => by
    intro x hx
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · have e₂ := hm₂ (ph, Ty.subst (synthBindings g.head) pg) (by simp)
      have e₁ := hm₁ (pg, Ty.subst Sf pf) (by simp)
      simp only at e₁ e₂ ⊢
      have hpgp := hg.plain pg (hpg pg (by simp))
      have hsc := hg.inScope pg (hpg pg (by simp))
      rw [subst_synth_stripConst g.head hg.types pg hpgp hsc] at e₂
      have := congrArg (Ty.unsynth σ₁) e₂
      rw [Ty.unsynth_subst h₁ σ₂ _ (Ty.plain_stripConst ph (hph ph (by simp))),
        unsynth_subst_synth g.head hg.types h₁ _ (Ty.plain_stripConst pg hpgp)
          (fun i hi => ⟨hsc i (by rwa [usedParams_stripConst] at hi),
            hb pg (by simp) i (by rwa [usedParams_stripConst] at hi)⟩)] at this
      rw [this, e₁]
    · exact compose_matches g hg Sf σ₁ σ₂ h₁ Ph Pg Pf (by simpa using hl₁) (by simpa using hl₂)
        (fun t ht => hph t (List.mem_cons_of_mem _ ht)) (fun t ht => hpg t (List.mem_cons_of_mem _ ht))
        (fun t ht => hb t (List.mem_cons_of_mem _ ht))
        (fun y hy => hm₁ y (by simp [hy])) (fun y hy => hm₂ y (by simp [hy])) x hx

/-- At least as specialized is transitive on the fragment. -/
theorem atLeastAsSpecialized_trans (ctx : Option Nat) (f g h : FunctionTemplate)
    (hf : Simple f) (hg : Simple g) (hh : Simple h)
    (h₁ : atLeastAsSpecialized f g ctx = true) (h₂ : atLeastAsSpecialized g h ctx = true) :
    atLeastAsSpecialized f h ctx = true := by
  rw [atLeast_simple ctx f g hf] at h₁
  rw [atLeast_simple ctx g h hg] at h₂
  rw [atLeast_simple ctx f h hf]
  unfold deduceAll transform at *
  simp only [List.length_map, bne_iff_ne, ne_eq, ite_not] at h₁ h₂ ⊢
  split at h₁
  · rename_i hl₁
    split at h₂
    · rename_i hl₂
      cases hgo₁ : deduceAll.go ((nominated g ctx).zip ((nominated f ctx).map (Ty.subst (synthBindings f.head)))) [] with
      | none => rw [hgo₁] at h₁; cases h₁
      | some σ₁ =>
        rw [hgo₁] at h₁
        cases hgo₂ : deduceAll.go ((nominated h ctx).zip ((nominated g ctx).map (Ty.subst (synthBindings g.head)))) [] with
        | none => rw [hgo₂] at h₂; cases h₂
        | some σ₂ =>
          rw [hgo₂] at h₂
          simp only [List.all_eq_true, List.mem_flatMap] at h₁ h₂
          have pf : ∀ t ∈ nominated f ctx, t.plain = true := fun t ht => hf.plain t (mem_nominated ht)
          have pg : ∀ t ∈ nominated g ctx, t.plain = true := fun t ht => hg.plain t (mem_nominated ht)
          have ph : ∀ t ∈ nominated h ctx, t.plain = true := fun t ht => hh.plain t (mem_nominated ht)
          have tf : ∀ t ∈ nominated f ctx, ∀ i ∈ usedParams t, i < f.head.length :=
            fun t ht => hf.inScope t (mem_nominated ht)
          have tg : ∀ t ∈ nominated g ctx, ∀ i ∈ usedParams t, i < g.head.length :=
            fun t ht => hg.inScope t (mem_nominated ht)
          have pp₁ : PlainPairs ((nominated g ctx).zip ((nominated f ctx).map (Ty.subst (synthBindings f.head)))) := by
            rintro ⟨p, a⟩ hx
            obtain ⟨hx₁, hx₂⟩ := List.of_mem_zip hx
            obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx₂
            exact ⟨pg _ hx₁, subst_synth_isRef f.head hf.types t (pf t ht) (tf t ht)⟩
          have pp₂ : PlainPairs ((nominated h ctx).zip ((nominated g ctx).map (Ty.subst (synthBindings g.head)))) := by
            rintro ⟨p, a⟩ hx
            obtain ⟨hx₁, hx₂⟩ := List.of_mem_zip hx
            obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx₂
            exact ⟨ph _ hx₁, subst_synth_isRef g.head hg.types t (pg t ht) (tg t ht)⟩
          have ty₁ := go_types _ [] σ₁ pp₁ (fun _ _ h => by cases h) hgo₁
          have ty₂ := go_types _ [] σ₂ pp₂ (fun _ _ h => by cases h) hgo₂
          have m₁ := (go_sound _ [] σ₁ pp₁ hgo₁).2
          have m₂ := (go_sound _ [] σ₂ pp₂ hgo₂).2
          have hc := compose_matches g hg (synthBindings f.head) σ₁ σ₂ ty₁ (nominated h ctx)
            (nominated g ctx) (nominated f ctx) (by simpa using hl₂) (by simpa using hl₁) ph
            (fun t ht => mem_nominated ht)
            (fun t ht i hi => h₁ i ⟨t, ht, hi⟩)
            (fun x hx => m₁ x hx σ₁ (Bindings.Sub.refl _))
            (fun x hx => m₂ x hx σ₂ (Bindings.Sub.refl _))
          have kτ : (σ₂.unsynth σ₁).Types := by
            intro i x hx
            rw [Bindings.lookup_unsynth] at hx
            obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hx
            rw [Ty.isType_unsynth ty₁]
            exact ty₂ i y hy
          have pp₃ : PlainPairs ((nominated h ctx).zip ((nominated f ctx).map (Ty.subst (synthBindings f.head)))) := by
            rintro ⟨p, a⟩ hx
            obtain ⟨hx₁, hx₂⟩ := List.of_mem_zip hx
            obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx₂
            exact ⟨ph _ hx₁, subst_synth_isRef f.head hf.types t (pf t ht) (tf t ht)⟩
          obtain ⟨σ', hgo, _⟩ := go_complete _ kτ.kinded _ [] pp₃
            (fun ⟨p, a⟩ hx => by
              refine ⟨hc _ hx, ?_⟩
              obtain ⟨_, hx₂⟩ := List.of_mem_zip hx
              obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx₂
              rw [subst_synth_stripConst f.head hf.types t (pf t ht) (tf t ht)]
              exact subst_synth_props f.head hf.types _ (Ty.plain_stripConst t (pf t ht))
                (by rw [usedParams_stripConst]; exact tf t ht))
            (fun _ _ h => by cases h)
          have hl₃ : (nominated h ctx).length = (nominated f ctx).length := by omega
          simp only [hl₃, ↓reduceIte, hgo, List.all_eq_true, List.mem_flatMap]
          rintro i ⟨t, ht, hi⟩
          obtain ⟨a, ha⟩ := mem_zip_left (as := (nominated f ctx).map (Ty.subst (synthBindings f.head)))
            (by simpa using hl₃) t ht
          exact go_binds _ [] σ' pp₃ hgo (t, a) ha i hi
    · cases h₂
  · cases h₁

/-- More specialized is transitive on the fragment. -/
@[std theorem "temp.func.order#2.sentence-4"]
theorem moreSpecialized_trans (ctx : Option Nat) (f g h : FunctionTemplate)
    (hf : Simple f) (hg : Simple g) (hh : Simple h)
    (h₁ : moreSpecialized ctx f g = true) (h₂ : moreSpecialized ctx g h = true) :
    moreSpecialized ctx f h = true := by
  refine moreSpecialized_trans_of ctx f g h ?_ h₁ h₂
  have hs : ∀ x ∈ [f, g, h], Simple x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  intro x hx y hy z hz hxy hyz
  exact atLeastAsSpecialized_trans ctx x y z (hs x hx) (hs y hy) (hs z hz) hxy hyz

end PartialOrdering

end Overload
