-- Overload/Generality.lean                                           -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Deduction

/-!
# Deduction is sound and most general

The exit criterion of phase 1. On the first-order fragment, where `P` is
built from names, template parameters, `const`, pointers, class template
specializations and constant arguments that are a parameter or mention
none, deduction is first-order matching:

* sound: substituting the bindings deduction returns into `P` gives `A`
  (`deduceTy_subst`);
* most general: any bindings that extend the starting ones and make `P`
  equal a non-dependent `A` extend what deduction returns
  (`deduceTy_most_general`).

Outside the fragment neither holds as stated. Reference collapsing makes
`T&` match `int&` with `T` as `int` or as `int&`. A constant argument
that mentions a parameter below the top is a non-deduced context
([temp.deduct.type]/5), so its parameter is left for substitution. The
call-site adjustments strip the top-level reference before deduction, so
the fragment covers what a call deduces for parameters such as `T`,
`const T&`, `T&&` and `C<T>*`.
-/

namespace Overload

/-- A value of the fragment: a constant template parameter, or a value
that mentions none. -/
def Val.firstOrder : Val → Bool
  | .param _ => true
  | v => !v.dependent

/-- A `P` of the fragment. -/
def Ty.firstOrder : Ty → Bool
  | .named _ | .nil | .param _ => true
  | .const t | .ptr t => Ty.firstOrder t
  | .spec _ as => Ty.firstOrder as
  | .cons a as => Ty.firstOrder a && Ty.firstOrder as
  | .value v => v.firstOrder
  | _ => false

/-- `σ ⊑ τ`: every binding of `σ` is a binding of `τ`. -/
def Bindings.Sub (σ τ : Bindings) : Prop :=
  ∀ i t, σ.lookup i = some t → τ.lookup i = some t

theorem Bindings.Sub.refl (σ : Bindings) : σ.Sub σ := fun _ _ h => h

theorem Bindings.Sub.trans {σ τ υ : Bindings} (h₁ : σ.Sub τ) (h₂ : τ.Sub υ) : σ.Sub υ :=
  fun i t h => h₂ i t (h₁ i t h)

theorem lookup_cons_self (i : ParamIdx) (a : Ty) (σ : Bindings) :
    Bindings.lookup ((i, a) :: σ) i = some a := by
  simp [Bindings.lookup]

theorem lookup_cons_other {i j : ParamIdx} (a : Ty) (σ : Bindings) (h : j ≠ i) :
    Bindings.lookup ((i, a) :: σ) j = σ.lookup j := by
  simp [Bindings.lookup, Ne.symm h]

theorem bindArg_spec {i : ParamIdx} {a : Ty} {σ σ' : Bindings} (h : bindArg i a σ = some σ') :
    σ'.lookup i = some a ∧ σ.Sub σ' := by
  unfold bindArg at h
  split at h
  · rename_i b hb
    split at h
    · rename_i hba
      simp only [Option.some.injEq] at h
      subst h hba
      exact ⟨hb, Bindings.Sub.refl _⟩
    · cases h
  · rename_i hn
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨lookup_cons_self i a σ, fun j t hj => ?_⟩
    by_cases hji : j = i
    · subst hji; rw [hn] at hj; cases hj
    · rw [lookup_cons_other a σ hji]; exact hj

/-- Binding a parameter to what a solution binds it to stays inside the
solution. -/
theorem bindArg_sub {i : ParamIdx} {a : Ty} {σ τ : Bindings} (hσ : σ.Sub τ)
    (hτ : τ.lookup i = some a) : ∃ σ', bindArg i a σ = some σ' ∧ σ'.Sub τ := by
  unfold bindArg
  cases hb : σ.lookup i with
  | some b =>
    have := hσ i b hb
    rw [hτ] at this
    cases this
    exact ⟨σ, by simp, hσ⟩
  | none =>
    refine ⟨(i, a) :: σ, rfl, fun j t hj => ?_⟩
    by_cases hji : j = i
    · subst hji; rw [lookup_cons_self] at hj; cases hj; exact hτ
    · rw [lookup_cons_other a σ hji] at hj; exact hσ j t hj

theorem Val.subst_of_not_dependent (σ : Bindings) : ∀ v : Val, v.dependent = false → v.subst σ = v
  | .int _, _ | .bool _, _ | .nil, _ => rfl
  | .obj c vs, h => by
    simp only [Val.dependent] at h
    simp only [Val.subst, Val.subst_of_not_dependent σ vs h]
  | .cons v vs, h => by
    simp only [Val.dependent, Bool.or_eq_false_iff] at h
    simp only [Val.subst, Val.subst_of_not_dependent σ v h.1, Val.subst_of_not_dependent σ vs h.2]
  | .param _, h => by simp [Val.dependent] at h

/-- Deduction keeps every binding it starts from. -/
theorem deduceTy_sub (p : Ty) : ∀ (a : Ty) (σ σ' : Bindings), deduceTy p a σ = some σ' → σ.Sub σ' := by
  induction p with
  | synth i => intro a σ σ' h; cases a <;> simp [deduceTy] at h
  | param i =>
    intro a σ σ' h
    simp only [deduceTy] at h
    split at h
    · exact (bindArg_spec h).2
    · cases h
  | value p =>
    intro a σ σ' h
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    unfold deduceVal at h
    split at h
    · exact (bindArg_spec h).2
    · split at h
      · simp only [Option.some.injEq] at h; subst h; exact Bindings.Sub.refl _
      · split at h
        · simp only [Option.some.injEq] at h; subst h; exact Bindings.Sub.refl _
        · cases h
  | cons p ps ihp ihps =>
    intro a σ σ' h
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    rename_i a as
    cases h₁ : deduceTy p a σ with
    | none => rw [h₁] at h; cases h
    | some σ₁ =>
      rw [h₁] at h
      exact (ihp a σ σ₁ h₁).trans (ihps as σ₁ σ' h)
  | fn ps r ne ihp ihr =>
    intro a σ σ' h
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    rename_i as s ne'
    split at h
    · cases h₁ : deduceTy ps as σ with
      | none => rw [h₁] at h; cases h
      | some σ₁ =>
        rw [h₁] at h
        exact (ihp as σ σ₁ h₁).trans (ihr s σ₁ σ' h)
    · exact absurd h (by simp)
  | const p ih | ptr p ih | lref p ih | rref p ih =>
    intro a σ σ' h
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    exact ih _ σ σ' h
  | spec c ps ih =>
    intro a σ σ' h
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    split at h
    · exact ih _ σ σ' h
    · cases h
  | named n =>
    intro a σ σ' h
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact Bindings.Sub.refl _
    · cases h
  | nil =>
    intro a σ σ' h
    cases a <;> simp only [deduceTy, reduceCtorEq, Option.some.injEq] at h
    subst h; exact Bindings.Sub.refl _
  | nondeduced _ _ | lookup _ _ _ | ref _ _ | removeCvref _ _ | typeOf _ _ | enableIf _ _ _ _ _ =>
    intro a σ σ' h
    simp only [deduceTy, Option.some.injEq] at h
    subst h; exact Bindings.Sub.refl _

/-- Soundness, in the form the induction needs: substituting any bindings
that extend what deduction returns into `P` gives `A`. -/
theorem deduceTy_subst_ext (p : Ty) (hp : p.firstOrder = true) :
    ∀ (a : Ty) (σ σ' : Bindings), deduceTy p a σ = some σ' → ∀ τ, σ'.Sub τ → Ty.subst τ p = a := by
  induction p with
  | param i =>
    intro a σ σ' h τ hτ
    simp only [deduceTy] at h
    split at h
    · rename_i ha
      have hl := hτ i a (bindArg_spec h).1
      simp only [Ty.subst, hl]
      cases a <;> simp_all [Ty.isType]
    · cases h
  | value p =>
    intro a σ σ' h τ hτ
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    rename_i a
    unfold deduceVal at h
    split at h
    · rename_i i
      have hl := hτ i _ (bindArg_spec h).1
      simp [Ty.subst, Val.subst, hl]
    · rename_i hnp
      have hnd : p.dependent = false := by
        cases p <;> simp_all [Ty.firstOrder, Val.firstOrder]
      simp only [hnd, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · rename_i heq
        subst heq
        simp [Ty.subst, Val.subst_of_not_dependent τ p hnd]
      · cases h
  | named n =>
    intro a σ σ' h τ _
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    split at h
    · rename_i heq; simp [Ty.subst, heq]
    · cases h
  | nil =>
    intro a σ σ' h τ _
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    rfl
  | const p ih =>
    intro a σ σ' h τ hτ
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    simp only [Ty.subst, ih (by simpa [Ty.firstOrder] using hp) _ σ σ' h τ hτ]
  | ptr p ih =>
    intro a σ σ' h τ hτ
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    simp only [Ty.subst, ih (by simpa [Ty.firstOrder] using hp) _ σ σ' h τ hτ]
  | spec c ps ih =>
    intro a σ σ' h τ hτ
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    split at h
    · rename_i heq
      simp only [Ty.subst, ih (by simpa [Ty.firstOrder] using hp) _ σ σ' h τ hτ, heq]
    · cases h
  | cons p ps ihp ihps =>
    intro a σ σ' h τ hτ
    simp only [Ty.firstOrder, Bool.and_eq_true] at hp
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    rename_i a as
    cases h₁ : deduceTy p a σ with
    | none => rw [h₁] at h; cases h
    | some σ₁ =>
      rw [h₁] at h
      have hs := deduceTy_sub ps as σ₁ σ' h
      simp only [Ty.subst, ihp hp.1 a σ σ₁ h₁ τ (hs.trans hτ), ihps hp.2 as σ₁ σ' h τ hτ]
  | lref _ _ | rref _ _ | nondeduced _ _ | lookup _ _ _ | ref _ _ | removeCvref _ _ | typeOf _ _
  | enableIf _ _ _ _ _ | fn _ _ _ _ _ | synth _ =>
    simp [Ty.firstOrder] at hp

/-- Soundness: on the fragment, substituting the bindings deduction returns
into `P` gives `A`. -/
@[std theorem "temp.deduct.type#1.sentence-1"]
theorem deduceTy_subst (p a : Ty) (σ σ' : Bindings) (hp : p.firstOrder = true)
    (h : deduceTy p a σ = some σ') : Ty.subst σ' p = a :=
  deduceTy_subst_ext p hp a σ σ' h σ' (Bindings.Sub.refl σ')

/-- Bindings that give each parameter a type or a value. -/
def Bindings.Kinded (τ : Bindings) : Prop :=
  ∀ i t, τ.lookup i = some t → t.isType = true ∨ ∃ v, t = .value v

/-- Most generality: on the fragment, any bindings `τ` that extend the
starting ones and make `P` equal a non-dependent `A` extend what
deduction returns, and deduction succeeds. -/
@[std theorem "temp.deduct.type#1.sentence-1"]
theorem deduceTy_most_general (p : Ty) (hp : p.firstOrder = true) :
    ∀ (a : Ty) (σ τ : Bindings), τ.Kinded → σ.Sub τ → Ty.subst τ p = a → a.dependent = false →
      ∃ σ', deduceTy p a σ = some σ' ∧ σ'.Sub τ := by
  induction p with
  | param i =>
    intro a σ τ hk hσ hs hd
    cases hl : τ.lookup i with
    | none => simp [Ty.subst, hl] at hs; subst hs; simp [Ty.dependent] at hd
    | some t =>
      rcases hk i t hl with ht | ⟨v, rfl⟩
      · have hta : t = a := by
          cases t <;> simp_all [Ty.subst, Ty.isType]
        subst hta
        obtain ⟨σ', hb, hsub⟩ := bindArg_sub hσ hl
        exact ⟨σ', by simp [deduceTy, ht, hb], hsub⟩
      · simp [Ty.subst, hl, Ty.isType] at hs; subst hs; simp [Ty.dependent] at hd
  | value p =>
    intro a σ τ hk hσ hs hd
    subst hs
    by_cases hpar : ∃ i, p = .param i
    · obtain ⟨i, rfl⟩ := hpar
      cases hl : τ.lookup i with
      | none => simp [Ty.subst, Val.subst, hl, Ty.dependent, Val.dependent] at hd
      | some t =>
        rcases hk i t hl with ht | ⟨v, rfl⟩
        · have : Val.subst τ (.param i) = .param i := by
            cases t <;> simp_all [Val.subst, Ty.isType]
          simp [Ty.subst, this, Ty.dependent, Val.dependent] at hd
        · obtain ⟨σ', hb, hsub⟩ := bindArg_sub hσ hl
          refine ⟨σ', ?_, hsub⟩
          simp only [Ty.subst, Val.subst, hl, deduceTy, deduceVal]
          exact hb
    · have hnd : p.dependent = false := by
        cases p <;> simp_all [Ty.firstOrder, Val.firstOrder]
      have hds : deduceVal p (Val.subst τ p) σ = some σ := by
        rw [Val.subst_of_not_dependent τ p hnd]
        unfold deduceVal
        split
        · rename_i i; exact absurd ⟨i, rfl⟩ hpar
        · simp [hnd]
      exact ⟨σ, by simp [Ty.subst, deduceTy, hds], hσ⟩
  | named n =>
    intro a σ τ _ hσ hs _
    subst hs
    exact ⟨σ, by simp [Ty.subst, deduceTy], hσ⟩
  | nil =>
    intro a σ τ _ hσ hs _
    subst hs
    exact ⟨σ, by simp [Ty.subst, deduceTy], hσ⟩
  | const p ih =>
    intro a σ τ hk hσ hs hd
    subst hs
    obtain ⟨σ', h, hsub⟩ := ih (by simpa [Ty.firstOrder] using hp) _ σ τ hk hσ rfl
      (by simpa [Ty.subst, Ty.dependent] using hd)
    exact ⟨σ', by simpa [Ty.subst, deduceTy] using h, hsub⟩
  | ptr p ih =>
    intro a σ τ hk hσ hs hd
    subst hs
    obtain ⟨σ', h, hsub⟩ := ih (by simpa [Ty.firstOrder] using hp) _ σ τ hk hσ rfl
      (by simpa [Ty.subst, Ty.dependent] using hd)
    exact ⟨σ', by simpa [Ty.subst, deduceTy] using h, hsub⟩
  | spec c ps ih =>
    intro a σ τ hk hσ hs hd
    subst hs
    obtain ⟨σ', h, hsub⟩ := ih (by simpa [Ty.firstOrder] using hp) _ σ τ hk hσ rfl
      (by simpa [Ty.subst, Ty.dependent] using hd)
    exact ⟨σ', by simpa [Ty.subst, deduceTy] using h, hsub⟩
  | cons p ps ihp ihps =>
    intro a σ τ hk hσ hs hd
    simp only [Ty.firstOrder, Bool.and_eq_true] at hp
    subst hs
    simp only [Ty.subst, Ty.dependent, Bool.or_eq_false_iff] at hd
    obtain ⟨σ₁, h₁, hsub₁⟩ := ihp hp.1 _ σ τ hk hσ rfl hd.1
    obtain ⟨σ', h₂, hsub⟩ := ihps hp.2 _ σ₁ τ hk hsub₁ rfl hd.2
    exact ⟨σ', by simp [Ty.subst, deduceTy, h₁, h₂], hsub⟩
  | lref _ _ | rref _ _ | nondeduced _ _ | lookup _ _ _ | ref _ _ | removeCvref _ _ | typeOf _ _
  | enableIf _ _ _ _ _ | fn _ _ _ _ _ | synth _ =>
    simp [Ty.firstOrder] at hp

end Overload
