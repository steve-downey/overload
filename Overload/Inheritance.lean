-- Overload/Inheritance.lean                                          -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Separability

/-!
# Inheritance between instance types

The plan's instance-inheritance question: may instance types for related
typeclasses be related by inheritance? Inheritance erasure is the
positive result. Erasing the base classes of a set of instance types `I`,
which is replacing derivation with composition plus retrieval, changes no
call that uses every class it touches at its exact type
(`inheritance_erasure`). Outside that fragment erasure changes outcomes
(`erasure_needs_exact_type`), and leak 1 is the way it does
(`rank_beats_refinement`).

The classes erasure touches are the ones in `I` and the ones derived from
one of them (`Program.touched`). Derivation from any other class is the
same before and after (`derivesWithin_erase`). A call uses the touched
classes at their exact type when every conversion it forms, between an
argument and a parameter, has the same class on both sides if either side
is touched (`ExactPair`).

Two parts of the plan's fragment are not modelled, so the theorem does not
cover them: deduction of a template parameter from a class derived from
the parameter's type ([temp.deduct.call]/4, leak 2), and access to a
protected base, which `derive_functor` uses.
-/

namespace Overload

/-! ## Erasing derivation -/

/-- Replace derivation by composition for the classes in `I`: each keeps
its definition and loses its base classes. -/
def Program.eraseBases (p : Program) (I : List String) : Program :=
  p.map fun
    | .class n bs => .class n (if I.contains n then [] else bs)
    | d => d

/-- The classes whose derivation erasing `I` can change: those in `I`, and
those derived from one. -/
def Program.touched (p : Program) (I : List String) : Ty → Bool
  | .named n => I.contains n || I.any fun c => p.derivesWithin p.length n c
  | _ => false

theorem eraseBases_length (p : Program) (I : List String) :
    (p.eraseBases I).length = p.length := by
  simp [Program.eraseBases]

theorem directBases_erase (p : Program) (I : List String) (d : String)
    (hd : I.contains d = false) :
    (p.eraseBases I).directBases d = p.directBases d := by
  unfold Program.directBases Program.eraseBases
  rw [List.findSome?_map]
  congr 2
  funext decl
  cases decl with
  | «class» n bs =>
    simp only [Function.comp]
    by_cases h : n = d
    · subst h
      have hn : n ∉ I := fun h => by rw [List.contains_iff_mem.mpr h] at hd; cases hd
      simp [hn]
    · simp [h]
  | _ => rfl

private theorem any_congr_mem {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- Derivation from a class erasure does not touch is unchanged: the
search never reaches a class in `I`. -/
theorem derivesWithin_erase (p : Program) (I : List String) :
    ∀ (k : Nat) (d b : String), I.contains d = false →
      (∀ c ∈ I, p.derivesWithin k d c = false) →
        (p.eraseBases I).derivesWithin k d b = p.derivesWithin k d b := by
  intro k
  induction k with
  | zero => intro d b _ _; rfl
  | succ k ih =>
    intro d b hd hc
    simp only [Program.derivesWithin, directBases_erase p I d hd]
    apply any_congr_mem
    intro m hm
    have hmI : I.contains m = false := by
      cases h : I.contains m with
      | false => rfl
      | true =>
        have := hc m (List.contains_iff_mem.mp h)
        simp only [Program.derivesWithin, List.any_eq_false] at this
        exact absurd (by simp) (this m hm)
    have hmc : ∀ c ∈ I, p.derivesWithin k m c = false := by
      intro c hcI
      have := hc c hcI
      simp only [Program.derivesWithin, List.any_eq_false] at this
      have := this m hm
      simp only [Bool.or_eq_true, beq_iff_eq, not_or] at this
      simpa using this.2
    rw [ih m b hmI hmc]

/-- Derivation from an untouched class is unchanged by erasure. -/
theorem derives_erase (p : Program) (I : List String) (s t : Ty)
    (hs : p.touched I s = false) :
    (p.eraseBases I).derives s t = p.derives s t := by
  cases s with
  | named d =>
    cases t with
    | named b =>
      simp only [Program.touched, Bool.or_eq_false_iff, List.any_eq_false] at hs
      simp only [Program.derives, eraseBases_length]
      exact derivesWithin_erase p I p.length d b hs.1 (fun c hc => by simpa using hs.2 c hc)
    | _ => rfl
  | _ => rfl

/-! ## Deduction depends on the environment's convertibility only at
non-dependent parameters -/

theorem form_congr {env₁ env₂ : Env} (h : env₁.instantiate = env₂.instantiate) (t : Ty) :
    form env₁ t = form env₂ t := by
  fun_induction form env₁ t <;> simp_all [form]

theorem formAll_congr {env₁ env₂ : Env} (h : env₁.instantiate = env₂.instantiate) :
    ∀ ts, formAll env₁ ts = formAll env₂ ts
  | [] => rfl
  | t :: ts => by simp only [formAll, form_congr h t, formAll_congr h ts]

theorem defaultsStep_congr {env₁ env₂ : Env} (h : env₁.instantiate = env₂.instantiate)
    (head : Head) : defaultsStep env₁ head = defaultsStep env₂ head := by
  funext σ
  simp only [defaultsStep]
  suffices ∀ (ps : Head) i σ, defaultsStep.go env₁ i ps σ = defaultsStep.go env₂ i ps σ from this _ _ _
  intro ps
  induction ps with
  | nil => intro i σ; rfl
  | cons q ps ih =>
    intro i σ
    simp only [defaultsStep.go, form_congr h, ih]

theorem nonDependentStep_congr {env₁ env₂ : Env} :
    ∀ (ps : List Ty) (args : List CallArg),
      (∀ x ∈ args.zip ps, x.2.dependent = false → env₁.convertible x.1 x.2 = env₂.convertible x.1 x.2) →
        nonDependentStep env₁ ps args = nonDependentStep env₂ ps args := by
  intro ps args h
  funext σ
  simp only [nonDependentStep]
  induction ps generalizing args with
  | nil => cases args <;> rfl
  | cons q ps ih =>
    cases args with
    | nil => rfl
    | cons a as =>
      have ih' := ih as (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp only [nonDependentStep.go]
      cases hd : q.dependent with
      | true => simpa using ih'
      | false =>
        have := h (a, q) List.mem_cons_self hd
        simp only [Bool.false_eq_true, ↓reduceIte, this, ih']

/-- Two environments that agree on instantiation and atomic constraints,
and on convertibility at the template's non-dependent parameters, give
the same deduction. -/
theorem deduceTemplate_congr {env₁ env₂ : Env} (hi : env₁.instantiate = env₂.instantiate)
    (ha : env₁.atomic = env₂.atomic) (ft : FunctionTemplate) (explicit : List Ty)
    (args : List CallArg)
    (hc : ∀ x ∈ args.zip ft.params, x.2.dependent = false →
      env₁.convertible x.1 x.2 = env₂.convertible x.1 x.2) :
    deduceTemplate env₁ ft explicit args = deduceTemplate env₂ ft explicit args := by
  have hp : parameterListStep env₁ ft.head = parameterListStep env₂ ft.head := by
    funext σ; simp only [parameterListStep, formAll_congr hi]
  have hk : constraintStep env₁ ft.constraint = constraintStep env₂ ft.constraint := by
    funext σ; simp only [constraintStep, ha]
  have hf : functionTypeStep env₁ ft = functionTypeStep env₂ ft := by
    funext σ; simp only [functionTypeStep, formAll_congr hi, form_congr hi]
  simp only [deduceTemplate, defaultsStep_congr hi, hp, hk, nonDependentStep_congr _ _ hc, hf]

/-! ## Erasure leaves lookup and constraints alone -/

theorem instancesOf_erase (p : Program) (I : List String) (tc : String) :
    (p.eraseBases I).instancesOf tc = p.instancesOf tc := by
  unfold Program.instancesOf Program.eraseBases
  rw [List.filterMap_map]
  congr 1
  funext d
  cases d <;> rfl

theorem selectInstance_erase (p : Program) (I : List String) (tc : String) (a : Ty) :
    (p.eraseBases I).selectInstance tc a = p.selectInstance tc a := by
  simp only [Program.selectInstance, instancesOf_erase]

theorem any_erase (p : Program) (I : List String) (f : Decl → Bool)
    (hf : ∀ n bs bs', f (.class n bs) = f (.class n bs')) :
    (p.eraseBases I).any f = p.any f := by
  unfold Program.eraseBases
  rw [List.any_map]
  apply any_congr_mem
  intro d _
  cases d with
  | «class» n bs => exact hf n _ bs
  | _ => rfl

theorem instantiate_erase (p : Program) (I : List String) (atomics : List (String × List Ty × Bool)) :
    (Env.ofProgram (p.eraseBases I) atomics).instantiate = (Env.ofProgram p atomics).instantiate := by
  funext n a
  simp only [Env.ofProgram, selectInstance_erase]
  rw [any_erase p I _ (fun _ _ _ => rfl), any_erase p I _ (fun _ _ _ => rfl)]

theorem atomic_erase (p : Program) (I : List String) (atomics : List (String × List Ty × Bool)) :
    (Env.ofProgram (p.eraseBases I) atomics).atomic = (Env.ofProgram p atomics).atomic := by
  funext e args
  simp only [Env.ofProgram, selectInstance_erase]

/-! ## Conversions at exact type do not see erasure -/

/-- A conversion between an argument and a parameter uses the touched
classes at their exact type: if either class is touched, they are the
same class. -/
def ExactPair (p : Program) (I : List String) (a : CallArg) (t : Ty) : Prop :=
  (p.touched I a.ty.referred.stripConst = true ∨ p.touched I t.referred.stripConst = true) →
    a.ty.referred.stripConst = t.referred.stripConst

theorem ExactPair.source {p : Program} {I : List String} {a : CallArg} {t : Ty}
    (h : ExactPair p I a t) :
    p.touched I a.ty.referred.stripConst = false ∨ a.ty.referred.stripConst = t.referred.stripConst := by
  cases ht : p.touched I a.ty.referred.stripConst with
  | false => exact .inl rfl
  | true => exact .inr (h (.inl ht))

theorem baseConv_erase (p : Program) (I : List String) (src tgt : Ty)
    (h : p.touched I src = false ∨ src = tgt) :
    (p.eraseBases I).baseConv src tgt = p.baseConv src tgt := by
  rcases h with h | h
  · simp only [Program.baseConv, derives_erase p I src tgt h]
  · subst h; simp [Program.baseConv]

theorem referenceCompatible_erase (p : Program) (I : List String) (t₁ t₂ : Ty)
    (h : p.touched I t₂.stripConst = false ∨ t₂.stripConst = t₁.stripConst) :
    (p.eraseBases I).referenceCompatible t₁ t₂ = p.referenceCompatible t₁ t₂ := by
  rcases h with h | h
  · simp only [Program.referenceCompatible, derives_erase p I _ _ h]
  · simp [Program.referenceCompatible, h]

theorem ics_erase (p : Program) (I : List String) (a : CallArg) (t : Ty) (h : ExactPair p I a t) :
    (p.eraseBases I).ics a t = p.ics a t := by
  have hs := h.source
  cases t with
  | lref u =>
    have hs' : _ ∨ a.ty.referred.stripConst = u.stripConst := hs
    simp only [Program.ics, referenceCompatible_erase p I u a.ty.referred hs',
      baseConv_erase p I _ _ hs']
  | rref u =>
    have hs' : _ ∨ a.ty.referred.stripConst = u.stripConst := hs
    simp only [Program.ics, referenceCompatible_erase p I u a.ty.referred hs',
      baseConv_erase p I _ _ hs']
  | _ => exact congrArg (Option.map _) (baseConv_erase p I _ _ hs)

theorem ics_spec (p : Program) (a : CallArg) (t : Ty) (s : StdConv) (h : p.ics a t = some s) :
    s.source = a.ty.referred.stripConst ∧ s.target = t.referred.stripConst ∧
      (s.rank = .conversion → s.source ≠ s.target) ∧
      (∀ b, s.binding = some b → b.referred.stripConst = s.target) := by
  have hb : ∀ src tgt r, p.baseConv src tgt = some r → r = .conversion → src ≠ tgt := by
    intro src tgt r h hr heq
    subst heq
    simp only [Program.baseConv, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at h
    subst h
    cases hr
  cases t
  case lref u =>
    simp only [Program.ics] at h
    split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h
      exact ⟨rfl, rfl, hb _ _ r hr, by intro b hb'; cases hb'; rfl⟩
    · cases h
  case rref u =>
    simp only [Program.ics] at h
    split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h
      exact ⟨rfl, rfl, hb _ _ r hr, by intro b hb'; cases hb'; rfl⟩
    · cases h
  all_goals
    simp only [Program.ics, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    exact ⟨rfl, rfl, hb _ _ r hr, by intro b hb'; cases hb'⟩

private theorem byRank_erase (p : Program) (I : List String) (s₁ s₂ : StdConv)
    (h₁ : s₁.rank = .conversion → p.touched I s₁.target = false)
    (h₂ : s₂.rank = .conversion → p.touched I s₂.source = false) :
    (p.eraseBases I).byRank s₁ s₂ = p.byRank s₁ s₂ := by
  unfold Program.byRank
  cases hr₁ : s₁.rank <;> cases hr₂ : s₂.rank
  · rfl
  · rfl
  · rfl
  · rw [derives_erase p I _ _ (h₁ hr₁), derives_erase p I _ _ (h₂ hr₂)]

private theorem byQualification_erase (p : Program) (I : List String) (s₁ s₂ : StdConv)
    (h : ∀ b₁ b₂, s₁.binding = some b₁ → s₂.binding = some b₂ →
      p.touched I b₁.referred.stripConst = false ∨ b₁.referred.stripConst = b₂.referred.stripConst) :
    (p.eraseBases I).byQualification s₁ s₂ = p.byQualification s₁ s₂ := by
  unfold Program.byQualification
  cases hb₁ : s₁.binding <;> cases hb₂ : s₂.binding
  · rfl
  · rfl
  · rfl
  · rename_i b₁ b₂
    simp only [referenceCompatible_erase p I _ _ (h b₁ b₂ hb₁ hb₂)]

/-- Two conversion sequences for one argument, each at exact type,
compare the same before and after erasure. -/
theorem better_erase (p : Program) (I : List String) (a : CallArg) (t₁ t₂ : Ty)
    (s₁ s₂ : StdConv) (he₁ : ExactPair p I a t₁) (he₂ : ExactPair p I a t₂)
    (h₁ : p.ics a t₁ = some s₁) (h₂ : p.ics a t₂ = some s₂) :
    (p.eraseBases I).better s₁ s₂ = p.better s₁ s₂ := by
  obtain ⟨hs₁, ht₁, hc₁, hb₁⟩ := ics_spec p a t₁ s₁ h₁
  obtain ⟨hs₂, ht₂, hc₂, hb₂⟩ := ics_spec p a t₂ s₂ h₂
  -- A Conversion has distinct classes, so neither is touched.
  have conv₁ : s₁.rank = .conversion →
      p.touched I s₁.source = false ∧ p.touched I s₁.target = false := by
    intro hr
    have hne := hc₁ hr
    constructor
    · cases ht : p.touched I s₁.source with
      | false => rfl
      | true => exact absurd (by rw [hs₁, ht₁]; exact he₁ (.inl (hs₁ ▸ ht))) hne
    · cases ht : p.touched I s₁.target with
      | false => rfl
      | true => exact absurd (by rw [hs₁, ht₁]; exact he₁ (.inr (ht₁ ▸ ht))) hne
  have conv₂ : s₂.rank = .conversion →
      p.touched I s₂.source = false ∧ p.touched I s₂.target = false := by
    intro hr
    have hne := hc₂ hr
    constructor
    · cases ht : p.touched I s₂.source with
      | false => rfl
      | true => exact absurd (by rw [hs₂, ht₂]; exact he₂ (.inl (hs₂ ▸ ht))) hne
    · cases ht : p.touched I s₂.target with
      | false => rfl
      | true => exact absurd (by rw [hs₂, ht₂]; exact he₂ (.inr (ht₂ ▸ ht))) hne
  -- A touched target is the argument's own class, so both targets are it.
  have targets : ∀ (u v : StdConv) (tu tv : Ty), ExactPair p I a tu → ExactPair p I a tv →
      u.target = tu.referred.stripConst → v.target = tv.referred.stripConst →
      p.touched I u.target = false ∨ u.target = v.target := by
    intro u v tu tv heu hev hu hv
    cases ht : p.touched I u.target with
    | false => exact .inl rfl
    | true =>
      right
      have h1 := heu (.inr (hu ▸ ht))
      have h2 := hev (.inl (by rw [h1, ← hu]; exact ht))
      rw [hu, hv, ← h1, ← h2]
  have q₁₂ := byQualification_erase p I s₁ s₂ (fun b₁ b₂ e₁ e₂ => by
    rw [hb₁ b₁ e₁, hb₂ b₂ e₂]; exact targets s₁ s₂ t₁ t₂ he₁ he₂ ht₁ ht₂)
  have q₂₁ := byQualification_erase p I s₂ s₁ (fun b₂ b₁ e₂ e₁ => by
    rw [hb₂ b₂ e₂, hb₁ b₁ e₁]; exact targets s₂ s₁ t₂ t₁ he₂ he₁ ht₂ ht₁)
  have r₁₂ := byRank_erase p I s₁ s₂ (fun h => (conv₁ h).2) (fun h => (conv₂ h).1)
  have r₂₁ := byRank_erase p I s₂ s₁ (fun h => (conv₂ h).2) (fun h => (conv₁ h).1)
  simp only [Program.better, Program.tiers, lexBetter, q₁₂, q₂₁, r₁₂, r₂₁]

/-! ## Resolution at exact type does not see erasure -/

/-- Two lists in step, related elementwise. -/
inductive Aligned (R : α → β → Prop) : List α → List β → Prop where
  | nil : Aligned R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      R a b → Aligned R as bs → Aligned R (a :: as) (b :: bs)

/-- A conversion sequence formed at exact type for an argument. -/
private def FormedAt (p : Program) (I : List String) (a : CallArg) (s : StdConv) : Prop :=
  ∃ t, ExactPair p I a t ∧ p.ics a t = some s

theorem conversions_erase (p : Program) (I : List String) :
    ∀ (args : List CallArg) (ps : List Ty), (∀ x ∈ args.zip ps, ExactPair p I x.1 x.2) →
      conversions (p.eraseBases I).ranking args ps = conversions p.ranking args ps := by
  intro args
  induction args with
  | nil => intro ps _; rfl
  | cons a as ih =>
    intro ps h
    cases ps with
    | nil => rfl
    | cons t ts =>
      have ha := h (a, t) List.mem_cons_self
      have ht := ih ts (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp only [conversions, ht]
      simp only [Program.ranking, ics_erase p I a t ha]

private theorem conversions_spec (p : Program) (I : List String) :
    ∀ (args : List CallArg) (ps : List Ty) (convs : List StdConv),
      (∀ x ∈ args.zip ps, ExactPair p I x.1 x.2) →
      conversions p.ranking args ps = .ok (some convs) →
        Aligned (FormedAt p I) args convs := by
  intro args
  induction args with
  | nil => intro ps convs _ h; cases h; exact .nil
  | cons a as ih =>
    intro ps convs hx h
    cases ps with
    | nil => cases h
    | cons t ts =>
      have ha := hx (a, t) List.mem_cons_self
      simp only [conversions] at h
      cases hi : p.ics a t with
      | none =>
        rw [show p.ranking.ics a t = .ok none from by simp [Program.ranking, hi]] at h
        cases h
      | some c =>
        rw [show p.ranking.ics a t = .ok (some c) from by simp [Program.ranking, hi]] at h
        simp only [Subst.bind_eq, Subst.bind_ok] at h
        cases hr : conversions p.ranking as ts with
        | ok o =>
          rw [hr] at h
          cases o with
          | none => cases h
          | some cs =>
            simp only [Subst.bind_ok, Subst.pure_eq, Subst.ok.injEq, Option.some.injEq] at h
            subst h
            exact .cons ⟨t, ha, hi⟩ (ih ts cs (fun x hx' => hx x (List.mem_cons_of_mem _ hx')) hr)
        | soft _ => rw [hr] at h; cases h
        | hard _ => rw [hr] at h; cases h

theorem viable_erase (p : Program) (I : List String) (args : List CallArg) :
    ∀ cs : List Candidate, (∀ c ∈ cs, ∀ x ∈ args.zip c.params, ExactPair p I x.1 x.2) →
      viable.go (p.eraseBases I).ranking args cs = viable.go p.ranking args cs := by
  intro cs
  induction cs with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro h
    have hc := conversions_erase p I args c.params (h c List.mem_cons_self)
    have ht := ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    simp only [viable.go, hc, ht]

private theorem viable_spec (p : Program) (I : List String) (args : List CallArg) :
    ∀ (cs : List Candidate) (vs : List (Viable StdConv)),
      (∀ c ∈ cs, ∀ x ∈ args.zip c.params, ExactPair p I x.1 x.2) →
      viable.go p.ranking args cs = .ok vs → ∀ v ∈ vs, Aligned (FormedAt p I) args v.convs := by
  intro cs
  induction cs with
  | nil => intro vs _ h; cases h; intro v hv; cases hv
  | cons c cs ih =>
    intro vs hx h
    have hx' := fun c' hc' => hx c' (List.mem_cons_of_mem _ hc')
    simp only [viable.go] at h
    split at h
    · cases hc : conversions p.ranking args c.params with
      | ok o =>
        rw [hc] at h
        cases o with
        | some convs =>
          cases hg : viable.go p.ranking args cs with
          | ok rest =>
            simp only [Subst.bind_eq, Subst.bind_ok, hg, Subst.pure_eq, Subst.ok.injEq] at h
            subst h
            intro v hv
            rcases List.mem_cons.mp hv with rfl | hv
            · exact conversions_spec p I args c.params convs (hx c List.mem_cons_self) hc
            · exact ih rest hx' hg v hv
          | soft _ => simp [hg] at h
          | hard _ => simp [hg] at h
        | none =>
          simp only [Subst.bind_eq, Subst.bind_ok] at h
          exact ih vs hx' h
      | soft _ => rw [hc] at h; cases h
      | hard _ => rw [hc] at h; cases h
    · exact ih vs hx' h

private theorem forall₂_zip {R : α → β → Prop} :
    ∀ {as : List α} {l₁ l₂ : List β}, Aligned R as l₁ → Aligned R as l₂ →
      ∀ x ∈ l₁.zip l₂, ∃ a, R a x.1 ∧ R a x.2
  | _, _, _, .nil, .nil => by intro x hx; cases hx
  | _, _, _, .cons h₁ t₁, .cons h₂ t₂ => by
    intro x hx
    simp only [List.zip_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨_, h₁, h₂⟩
    · exact forall₂_zip t₁ t₂ x hx

private theorem all_congr_mem {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem betterFunction_erase (p : Program) (I : List String) (args : List CallArg)
    (ms : Specialization → Specialization → Bool) (f₁ f₂ : Viable StdConv)
    (h₁ : Aligned (FormedAt p I) args f₁.convs) (h₂ : Aligned (FormedAt p I) args f₂.convs) :
    betterFunction (p.eraseBases I).ranking ms f₁ f₂ = betterFunction p.ranking ms f₁ f₂ := by
  have hb : ∀ x ∈ f₁.convs.zip f₂.convs,
      (p.eraseBases I).better x.1 x.2 = p.better x.1 x.2 ∧
        (p.eraseBases I).better x.2 x.1 = p.better x.2 x.1 := by
    intro x hx
    obtain ⟨a, ⟨t₁, e₁, i₁⟩, ⟨t₂, e₂, i₂⟩⟩ := forall₂_zip h₁ h₂ x hx
    exact ⟨better_erase p I a t₁ t₂ _ _ e₁ e₂ i₁ i₂, better_erase p I a t₂ t₁ _ _ e₂ e₁ i₂ i₁⟩
  have hall := all_congr_mem (l := f₁.convs.zip f₂.convs)
    (f := fun (c₁, c₂) => !(p.eraseBases I).better c₂ c₁) (g := fun (c₁, c₂) => !p.better c₂ c₁)
    (fun x hx => by obtain ⟨c₁, c₂⟩ := x; simp only [(hb (c₁, c₂) hx).2])
  have hany := any_congr_mem (l := f₁.convs.zip f₂.convs)
    (f := fun (c₁, c₂) => (p.eraseBases I).better c₁ c₂) (g := fun (c₁, c₂) => p.better c₁ c₂)
    (fun x hx => by obtain ⟨c₁, c₂⟩ := x; simp only [(hb (c₁, c₂) hx).1])
  simp only [betterFunction, Program.ranking, hall, hany]

theorem bestViable_congr (r₁ : Ranking C₁) (r₂ : Ranking C₁)
    (ms : Specialization → Specialization → Bool) (vs : List (Viable C₁))
    (h : ∀ w ∈ vs, ∀ f ∈ vs, betterFunction r₁ ms w f = betterFunction r₂ ms w f) :
    bestViable r₁ ms vs = bestViable r₂ ms vs := by
  have hf : vs.filter (fun w => vs.all fun f => f.cand.index == w.cand.index || betterFunction r₁ ms w f) =
      vs.filter (fun w => vs.all fun f => f.cand.index == w.cand.index || betterFunction r₂ ms w f) :=
    List.filter_congr fun w hw => all_congr_mem fun f hf => by rw [h w hw f hf]
  unfold bestViable
  simp only [hf]

/-- Inheritance erasure: erasing the base classes of the instance types in
`I`, which replaces derivation by composition, changes no call that uses
every class erasure touches at its exact type. The hypotheses ask it of
each conversion the call can form: at the non-dependent parameters that
deduction checks, and at every parameter of every candidate. -/
theorem inheritance_erasure (mode : Mode) (p : Program) (I : List String)
    (atomics : List (String × List Ty × Bool)) (decls : List Decl) (args : List CallArg)
    (explicit : List Ty)
    (hdeduce : ∀ ft, .functionTemplate ft ∈ decls → ∀ x ∈ args.zip ft.params,
      x.2.dependent = false → ExactPair p I x.1 x.2)
    (huse : ∀ cs, generate mode (Env.ofProgram p atomics) decls args explicit = .ok cs →
      ∀ c ∈ cs, ∀ x ∈ args.zip c.params, ExactPair p I x.1 x.2) :
    resolve mode (Env.ofProgram (p.eraseBases I) atomics) (p.eraseBases I).ranking decls args explicit =
      resolve mode (Env.ofProgram p atomics) p.ranking decls args explicit := by
  have hgen : generate mode (Env.ofProgram (p.eraseBases I) atomics) decls args explicit =
      generate mode (Env.ofProgram p atomics) decls args explicit := by
    simp only [generate]
    refine generate_go_congr _ _ args explicit _ decls (fun ft hm => ?_) 0
    refine deduceTemplate_congr (instantiate_erase p I atomics) (atomic_erase p I atomics) ft
      explicit args (fun x hx hd => ?_)
    simp only [Env.ofProgram, ics_erase p I x.1 x.2 (hdeduce ft hm x hx hd)]
  unfold resolve
  rw [hgen]
  cases hg : generate mode (Env.ofProgram p atomics) decls args explicit with
  | ok cs =>
    have hcs := huse cs hg
    simp only [viable, viable_erase p I args cs hcs]
    cases hv : viable.go p.ranking args cs with
    | ok vs =>
      apply bestViable_congr
      intro w hw f hf
      exact betterFunction_erase p I args _ w f (viable_spec p I args cs vs hcs hv w hw)
        (viable_spec p I args cs vs hcs hv f hf)
    | soft _ => rfl
    | hard _ => rfl
  | soft _ => rfl
  | hard _ => rfl

/-! ## Outside exact-type use, erasure changes the outcome -/

/-- An Applicative instance type derived from a Functor one, and a
function that names the Functor instance type. -/
def namedBase : Program :=
  [ .class "functor_i", .class "applicative_i" ["functor_i"]
  , .function "use" [.lref (.const (.named "functor_i"))] ]

/-- Erasure needs exact-type use: a function naming the base instance type
accepts the derived one by a derived-to-base conversion, and after
erasure it accepts nothing. The conversion is not at exact type, so
`inheritance_erasure` does not apply. -/
theorem erasure_needs_exact_type :
    (resolve .text (Env.ofProgram namedBase) namedBase.ranking (namedBase.candidates "use")
        [{ ty := .named "applicative_i", lvalue := true }]).map (·.index) = .selected 0 ∧
      (resolve .text (Env.ofProgram (namedBase.eraseBases ["applicative_i"]))
        (namedBase.eraseBases ["applicative_i"]).ranking
        ((namedBase.eraseBases ["applicative_i"]).candidates "use")
        [{ ty := .named "applicative_i", lvalue := true }]).map (·.index) = .noMatch := by
  constructor <;> rfl

/-! ## Superclass coherence is a law, not an identity -/

/-- A Functor retrieved from a stronger instance, `derive_functor<M>`, is
a different object from the canonical Functor instance, so pinning one
or the other gives different specializations of the same template. The
two can agree only in behaviour, which the language does not check:
superclass coherence is an obligation on instance authors. -/
theorem superclass_identity (env : Env) (tc name canonical derived : String) (c : Ty)
    (x : CallArg) (hc : c.isType = true) (hcd : c.dependent = false) (hcF : c.formed = true)
    (hcr : c.isRef = false) (hne : canonical ≠ derived) :
    deduceTemplate env (pinTemplate tc name) [c, .ref (.named canonical)] [x] ≠
      deduceTemplate env (pinTemplate tc name) [c, .ref (.named derived)] [x] := by
  rw [pinned_deduce env tc name canonical c x hc hcd hcF hcr,
    pinned_deduce env tc name derived c x hc hcd hcF hcr]
  intro h
  simp [pinSpec] at h
  exact hne h

end Overload
