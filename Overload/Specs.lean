-- Overload/Specs.lean                                                -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Transitivity
import Overload.Resolution

/-!
# Relation forms for ordering and resolution

The `spec-style` convention gives each mechanism twice, as an inductive
relation that transcribes the Standard and as an executable function,
with an agreement theorem. Partial ordering of function templates and
overload resolution were functions only. Here are their relations, built
on the relation for deduction (`DeduceTy`), and the agreement theorems:

* `DeducePairs` and `deduceAll_go_iff`: the pairs of partial ordering,
  deduced in turn;
* `AtLeastAsSpecialized` and `atLeastAsSpecialized_iff`
  ([temp.deduct.partial]/10);
* `MoreSpecialized` and `moreSpecialized_iff` ([temp.deduct.partial]/10,
  [temp.func.order]/8);
* `BetterFunction` and `betterFunction_iff` ([over.match.best.general]/2);
* `BestViable` and `bestViable_iff` ([over.match.best.general]/3);
* `Resolves` and `resolve_iff`.
-/

namespace Overload

namespace PartialOrdering

theorem deducePair_fst (p a : Ty) (σ : Bindings) :
    (deducePair p a σ).1 = deduceTy p.referred.stripConst a.referred.stripConst σ := by
  unfold deducePair
  dsimp only
  cases deduceTy p.referred.stripConst a.referred.stripConst σ <;> rfl

/-- The nominated pairs of partial ordering, deduced in turn, each with the
references and top-level cv-qualifiers removed, and the bindings shared. -/
@[specification]
inductive DeducePairs : List (Ty × Ty) → Bindings → Bindings → Prop where
  | nil (σ : Bindings) : DeducePairs [] σ σ
  | cons {p a : Ty} {rest : List (Ty × Ty)} {σ σ₁ σ' : Bindings} :
      DeduceTy p.referred.stripConst a.referred.stripConst σ σ₁ → DeducePairs rest σ₁ σ' →
      DeducePairs ((p, a) :: rest) σ σ'

attribute [std rule "temp.deduct.partial#12.sentence-1"] DeducePairs.nil
attribute [std rule "temp.deduct.partial#5"] DeducePairs.cons

theorem deduceAll_go_iff : ∀ (pairs : List (Ty × Ty)) (σ σ' : Bindings),
    deduceAll.go pairs σ = some σ' ↔ DeducePairs pairs σ σ'
  | [], σ, σ' => by
    constructor
    · intro h; simp only [deduceAll.go, Option.some.injEq] at h; subst h; exact .nil σ
    · intro h; cases h; rfl
  | (p, a) :: rest, σ, σ' => by
    constructor
    · intro h
      simp only [deduceAll.go] at h
      cases hd : deducePair p a σ with
      | mk o b =>
        rw [hd] at h
        cases o with
        | none => cases h
        | some σ₁ =>
          have h₁ : deduceTy p.referred.stripConst a.referred.stripConst σ = some σ₁ := by
            rw [← deducePair_fst, hd]
          exact .cons ((deduceTy_iff _ _ _ _).2 h₁) ((deduceAll_go_iff rest σ₁ σ').1 h)
    · intro h
      cases h with
      | cons h₁ h₂ =>
        rename_i σ₁
        have e : (deducePair p a σ).1 = some σ₁ := by
          rw [deducePair_fst]; exact (deduceTy_iff _ _ _ _).1 h₁
        simp only [deduceAll.go]
        cases hd : deducePair p a σ with
        | mk o b =>
          rw [hd] at e
          simp only at e
          subst e
          exact (deduceAll_go_iff rest σ₁ σ').2 h₂

/-- `F` is at least as specialized as `G`: deduction of `G`'s nominated
types from `F`'s transformed ones succeeds for every pair, binding every
template parameter the nominated types use, and no pair of the opposite
direction denies it by the tie-breaks of /9. -/
@[specification]
inductive AtLeastAsSpecialized (f g : FunctionTemplate) (ctx : Option Nat) : Prop where
  | intro (σ : Bindings) :
      (nominated g ctx).length = (transform f.head (nominated f ctx)).length →
      DeducePairs ((nominated g ctx).zip (transform f.head (nominated f ctx))) [] σ →
      (∀ t ∈ nominated g ctx, ∀ i ∈ usedParams t, (σ.lookup i).isSome = true) →
      (∀ x ∈ (nominated f ctx).zip (transform g.head (nominated g ctx)), denies x.1 x.2 = false) →
      AtLeastAsSpecialized f g ctx

attribute [std rule "temp.deduct.partial#10.sentence-1"] AtLeastAsSpecialized.intro

theorem atLeastAsSpecialized_iff (f g : FunctionTemplate) (ctx : Option Nat) :
    atLeastAsSpecialized f g ctx = true ↔ AtLeastAsSpecialized f g ctx := by
  unfold atLeastAsSpecialized direction deduceAll
  constructor
  · intro h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨h₁, h₂⟩ := h
    split at h₁
    · cases h₁
    · rename_i hl
      cases hg : deduceAll.go ((nominated g ctx).zip (transform f.head (nominated f ctx))) [] with
      | none => rw [hg] at h₁; cases h₁
      | some σ =>
        rw [hg] at h₁
        refine .intro σ (by simpa using hl) ((deduceAll_go_iff _ _ _).1 hg) ?_ ?_
        · simpa [List.all_eq_true] using h₁
        · intro x hx
          rw [List.any_eq_false] at h₂
          obtain ⟨p, a⟩ := x
          simpa using h₂ (p, a) hx
  · rintro ⟨σ, hl, hd, hb, hn⟩
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨?_, ?_⟩
    · have hl' : ¬ ((nominated g ctx).length != (transform f.head (nominated f ctx)).length) = true := by
        simpa using hl
      simp only [hl', Bool.false_eq_true, ↓reduceIte, (deduceAll_go_iff _ _ _).2 hd]
      simpa [List.all_eq_true] using hb
    · rw [List.any_eq_false]
      intro x hx
      obtain ⟨p, a⟩ := x
      simpa using hn (p, a) hx

instance (f g : FunctionTemplate) (ctx : Option Nat) : Decidable (AtLeastAsSpecialized f g ctx) :=
  decidable_of_iff _ (atLeastAsSpecialized_iff f g ctx)

/-- `F` is more specialized than `G`: by deduction alone, or, each being at
least as specialized as the other, by constraints through the gate of
[temp.func.order]/8. -/
@[specification]
inductive MoreSpecialized (ctx : Option Nat) (f g : FunctionTemplate) : Prop where
  | byDeduction : AtLeastAsSpecialized f g ctx → ¬ AtLeastAsSpecialized g f ctx → MoreSpecialized ctx f g
  | byConstraints : AtLeastAsSpecialized f g ctx → AtLeastAsSpecialized g f ctx →
      tieBreakApplies f g = true → Constraint.moreConstrained f.constraint g.constraint = true →
      MoreSpecialized ctx f g

attribute [std rule "temp.deduct.partial#10.sentence-2"] MoreSpecialized.byDeduction
attribute [std rule "temp.func.order#8"] MoreSpecialized.byConstraints

theorem moreSpecialized_iff (ctx : Option Nat) (f g : FunctionTemplate) :
    moreSpecialized ctx f g = true ↔ MoreSpecialized ctx f g := by
  simp only [moreSpecialized, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro (⟨h₁, h₂⟩ | ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩)
    · exact .byDeduction ((atLeastAsSpecialized_iff _ _ _).1 h₁) (by
        rw [← atLeastAsSpecialized_iff, h₂]; simp)
    · exact .byConstraints ((atLeastAsSpecialized_iff _ _ _).1 h₁)
        ((atLeastAsSpecialized_iff _ _ _).1 h₂) h₃ h₄
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂, h₃, h₄⟩)
    · left
      refine ⟨(atLeastAsSpecialized_iff _ _ _).2 h₁, ?_⟩
      cases h : atLeastAsSpecialized g f ctx with
      | false => rfl
      | true => exact absurd ((atLeastAsSpecialized_iff _ _ _).1 h) h₂
    · right
      exact ⟨⟨⟨(atLeastAsSpecialized_iff _ _ _).2 h₁, (atLeastAsSpecialized_iff _ _ _).2 h₂⟩, h₃⟩, h₄⟩

end PartialOrdering

/-! ## Overload resolution -/

/-- No conversion sequence of `F₂` is better than the corresponding one of
`F₁`. -/
def NotWorse (r : Ranking Conv) (f₁ f₂ : Viable Conv) : Prop :=
  ∀ x ∈ f₁.convs.zip f₂.convs, r.better x.2 x.1 = false

/-- `F₁` is a better function than `F₂`: not worse for any argument, and
better for some argument, or a non-template against a template
specialization, or the more specialized template. -/
@[specification]
inductive BetterFunction (r : Ranking Conv) (ms : Specialization → Specialization → Bool)
    (f₁ f₂ : Viable Conv) : Prop where
  | betterConversion : NotWorse r f₁ f₂ → (∃ x ∈ f₁.convs.zip f₂.convs, r.better x.1 x.2 = true) →
      BetterFunction r ms f₁ f₂
  | nonTemplate : NotWorse r f₁ f₂ → f₁.cand.isTemplate = false → f₂.cand.isTemplate = true →
      BetterFunction r ms f₁ f₂
  | moreSpecialized {s₁ s₂ : Specialization} : NotWorse r f₁ f₂ → f₁.cand.specialization = some s₁ →
      f₂.cand.specialization = some s₂ → ms s₁ s₂ = true → BetterFunction r ms f₁ f₂

attribute [std rule "over.match.best.general#2"] BetterFunction.betterConversion
attribute [std rule "over.match.best.general#2"] BetterFunction.nonTemplate
attribute [std rule "over.match.best.general#2"] BetterFunction.moreSpecialized

theorem betterFunction_iff (r : Ranking Conv) (ms : Specialization → Specialization → Bool)
    (f₁ f₂ : Viable Conv) : betterFunction r ms f₁ f₂ = true ↔ BetterFunction r ms f₁ f₂ := by
  have hnw : ((f₁.convs.zip f₂.convs).all fun (c₁, c₂) => !r.better c₂ c₁) = true ↔ NotWorse r f₁ f₂ := by
    simp only [List.all_eq_true, NotWorse, Bool.not_eq_true']
  have hsb : ((f₁.convs.zip f₂.convs).any fun (c₁, c₂) => r.better c₁ c₂) = true ↔
      ∃ x ∈ f₁.convs.zip f₂.convs, r.better x.1 x.2 = true := by
    simp only [List.any_eq_true]
  unfold betterFunction
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨h₁, (h₂ | ⟨h₃, h₄⟩) | h₅⟩
    · exact .betterConversion (hnw.1 h₁) (hsb.1 h₂)
    · exact .nonTemplate (hnw.1 h₁) h₃ h₄
    · split at h₅
      · rename_i s₁ s₂ e₁ e₂
        exact .moreSpecialized (hnw.1 h₁) e₁ e₂ h₅
      · cases h₅
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₃, h₄⟩ | ⟨h₁, e₁, e₂, h₅⟩)
    · exact ⟨hnw.2 h₁, .inl (.inl (hsb.2 h₂))⟩
    · exact ⟨hnw.2 h₁, .inl (.inr ⟨h₃, h₄⟩)⟩
    · refine ⟨hnw.2 h₁, .inr ?_⟩
      rw [e₁, e₂]
      exact h₅

instance (r : Ranking Conv) (ms : Specialization → Specialization → Bool) (f₁ f₂ : Viable Conv) :
    Decidable (BetterFunction r ms f₁ f₂) :=
  decidable_of_iff _ (betterFunction_iff r ms f₁ f₂)

/-- `W` is better than every other viable function. -/
def IsBest (r : Ranking Conv) (ms : Specialization → Specialization → Bool) (vs : List (Viable Conv))
    (w : Viable Conv) : Prop :=
  ∀ f ∈ vs, f.cand.index = w.cand.index ∨ BetterFunction r ms w f

instance (r : Ranking Conv) (ms : Specialization → Specialization → Bool) (vs : List (Viable Conv))
    (w : Viable Conv) : Decidable (IsBest r ms vs w) := by
  unfold IsBest; infer_instance

/-- The best viable function: none viable is no match; exactly one viable
function better than all the others is selected; otherwise the call is
ambiguous, among the best if there are several, among all if there is
none. -/
@[specification]
inductive BestViable (r : Ranking Conv) (ms : Specialization → Specialization → Bool) :
    List (Viable Conv) → Resolution Candidate → Prop where
  | noViable : BestViable r ms [] .noMatch
  | selected {vs : List (Viable Conv)} {w : Viable Conv} : vs ≠ [] →
      vs.filter (fun v => decide (IsBest r ms vs v)) = [w] → BestViable r ms vs (.selected w.cand)
  | noneBest {vs : List (Viable Conv)} : vs ≠ [] → vs.filter (fun v => decide (IsBest r ms vs v)) = [] →
      BestViable r ms vs (.ambiguous (vs.map (·.cand)))
  | severalBest {vs ws : List (Viable Conv)} : vs ≠ [] →
      vs.filter (fun v => decide (IsBest r ms vs v)) = ws → 2 ≤ ws.length →
      BestViable r ms vs (.ambiguous (ws.map (·.cand)))

attribute [std rule "over.match.general#3.sentence-2"] BestViable.noViable
attribute [std rule "over.match.best.general#3.sentence-1"] BestViable.selected
attribute [std rule "over.match.best.general#3.sentence-1"] BestViable.noneBest
attribute [std rule "over.match.best.general#3.sentence-1"] BestViable.severalBest

theorem bestFilter_eq (r : Ranking Conv) (ms : Specialization → Specialization → Bool)
    (vs : List (Viable Conv)) :
    vs.filter (fun w => vs.all fun f => f.cand.index == w.cand.index || betterFunction r ms w f) =
      vs.filter (fun v => decide (IsBest r ms vs v)) := by
  apply List.filter_congr
  intro w _
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [List.all_eq_true, IsBest, Bool.or_eq_true, beq_iff_eq, betterFunction_iff]

theorem bestViable_iff (r : Ranking Conv) (ms : Specialization → Specialization → Bool)
    (vs : List (Viable Conv)) (res : Resolution Candidate) :
    bestViable r ms vs = res ↔ BestViable r ms vs res := by
  cases vs with
  | nil =>
    simp only [bestViable]
    constructor
    · rintro rfl; exact .noViable
    · intro h
      cases h with
      | noViable => rfl
      | selected hne _ => exact absurd rfl hne
      | noneBest hne _ => exact absurd rfl hne
      | severalBest hne _ _ => exact absurd rfl hne
  | cons v vs' =>
    have hne : (v :: vs') ≠ [] := List.cons_ne_nil _ _
    unfold bestViable
    simp only
    rw [bestFilter_eq]
    generalize hB : (v :: vs').filter (fun u => decide (IsBest r ms (v :: vs') u)) = B
    constructor
    · intro h
      cases B with
      | nil => rw [← h]; exact .noneBest hne hB
      | cons w ws =>
        cases ws with
        | nil => rw [← h]; exact .selected hne hB
        | cons w' ws => rw [← h]; exact .severalBest hne hB (by simp)
    · intro h
      cases h with
      | selected _ e => rw [hB] at e; rw [e]
      | noneBest _ e => rw [hB] at e; rw [e]
      | severalBest _ e hl =>
        rw [hB] at e
        subst e
        cases B with
        | nil => simp at hl
        | cons w ws =>
          cases ws with
          | nil => simp at hl
          | cons w' ws => rfl

/-- Overload resolution: candidate generation, which may be ill-formed;
then the viable functions, whose conversions may be ill-formed; then the
best viable function. -/
@[specification]
inductive Resolves (mode : Mode) (env : Env) (r : Ranking Conv) (decls : List Decl)
    (args : List CallArg) (explicit : List Ty) : Resolution Candidate → Prop where
  | generationHard {e : Reason} : generate mode env decls args explicit = .hard e →
      Resolves mode env r decls args explicit (.illFormed e)
  | generationSoft {e : Reason} : generate mode env decls args explicit = .soft e →
      Resolves mode env r decls args explicit (.illFormed e)
  | viabilityHard {cs : List Candidate} {e : Reason} : generate mode env decls args explicit = .ok cs →
      viable r cs args = .hard e → Resolves mode env r decls args explicit (.illFormed e)
  | viabilitySoft {cs : List Candidate} {e : Reason} : generate mode env decls args explicit = .ok cs →
      viable r cs args = .soft e → Resolves mode env r decls args explicit (.illFormed e)
  | best {cs : List Candidate} {vs : List (Viable Conv)} {res : Resolution Candidate} :
      generate mode env decls args explicit = .ok cs → viable r cs args = .ok vs →
      BestViable r (orderingForCall args.length) vs res → Resolves mode env r decls args explicit res

attribute [std rule "temp.deduct.general#8.sentence-3"] Resolves.generationHard
attribute [std rule "over.match.funcs.general#8.sentence-1"] Resolves.generationSoft
attribute [std rule "over.match.viable#4.sentence-1"] Resolves.viabilityHard
attribute [std rule "over.match.viable#4.sentence-1"] Resolves.viabilitySoft
attribute [std rule "over.match.best.general#3.sentence-1"] Resolves.best

theorem resolve_iff (mode : Mode) (env : Env) (r : Ranking Conv) (decls : List Decl)
    (args : List CallArg) (explicit : List Ty) (res : Resolution Candidate) :
    resolve mode env r decls args explicit = res ↔ Resolves mode env r decls args explicit res := by
  unfold resolve
  constructor
  · intro h
    cases hg : generate mode env decls args explicit with
    | hard e => rw [hg] at h; rw [← h]; exact .generationHard hg
    | soft e => rw [hg] at h; rw [← h]; exact .generationSoft hg
    | ok cs =>
      rw [hg] at h
      simp only at h
      cases hv : viable r cs args with
      | hard e => rw [hv] at h; rw [← h]; exact .viabilityHard hg hv
      | soft e => rw [hv] at h; rw [← h]; exact .viabilitySoft hg hv
      | ok vs =>
        rw [hv] at h
        exact .best hg hv ((bestViable_iff _ _ _ _).1 h)
  · intro h
    cases h with
    | generationHard hg => rw [hg]
    | generationSoft hg => rw [hg]
    | viabilityHard hg hv => rw [hg]; simp only; rw [hv]
    | viabilitySoft hg hv => rw [hg]; simp only; rw [hv]
    | best hg hv hb => rw [hg]; simp only; rw [hv]; exact (bestViable_iff _ _ _ _).2 hb

end Overload
