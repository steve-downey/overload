-- Overload/Mandates.lean                                             -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Separability

/-!
# Mandates

A Mandate is a condition that, if not met, makes the program ill-formed
([structure.specifications]/3). The library's wording says it may be a
`static_assert` in the body, so it is checked only once overload
resolution has selected the function and its definition is instantiated.
The model reads it that way, as the plan's phase 2 asked: `invoke` is
resolution followed by the selected specialization's Mandates.

Two of the plan's target theorems are about Mandates.

* mandate-inertness holds. A Mandate never changes which candidate is
  selected (`mandate_inertness`), and at the call it only turns a
  selection into an ill-formed program (`invoke_selected`).
* constraint-promotion holds in part. Promoting a Mandate to a
  constraint removes the candidate where the Mandate fails, so the call
  moves to the resolution without it (`constraint_promotion`). Where the
  Mandate holds the candidate stays, but its constraint has grown, so
  partial ordering can change. The theorem needs the ordering not to
  change, and without that the outcome can move to a candidate that
  removal would not give (`promotion_reorders`).
-/

namespace Overload

/-! ## Deduction does not read the Mandates -/

/-- The specialization of the same template with different Mandates. -/
def Specialization.withTemplate (ft : FunctionTemplate) (sp : Specialization) : Specialization :=
  { sp with template := ft }

theorem deduceTemplate_mandate (env : Env) (ft : FunctionTemplate) (m : Option Constraint)
    (explicit : List Ty) (args : List CallArg) :
    deduceTemplate env { ft with mandate := m } explicit args =
      (deduceTemplate env ft explicit args).map (Specialization.withTemplate { ft with mandate := m }) := by
  unfold deduceTemplate
  generalize explicitStep ft.head explicit >>= callStep env ft.params args >>= defaultsStep env ft.head
    >>= parameterListStep env ft.head >>= constraintStep env ft.constraint
    >>= nonDependentStep env ft.params args = pre
  cases pre with
  | ok σ =>
    simp only [Subst.bind_eq, Subst.bind_ok, functionTypeStep]
    cases formAll env (ft.params.map (Ty.subst σ)) with
    | ok ps =>
      simp only [Subst.bind_ok]
      cases form env (ft.ret.subst σ) <;> rfl
    | soft _ => rfl
    | hard _ => rfl
  | soft _ => rfl
  | hard _ => rfl

/-! ## Candidate generation, one declaration at a time -/

/-- What one declaration contributes to the candidates at position `i`,
under the text: a candidate, nothing, or a hard error. -/
def contribution (env : Env) (args : List CallArg) (explicit : List Ty) : Decl → Nat →
    Subst (Option Candidate)
  | .function _ ps _, i => .ok (some { index := i, params := ps })
  | .functionTemplate ft, i =>
    match deduceTemplate env ft explicit args with
    | .ok sp => .ok (some { index := i, params := sp.params, defaultArgs := ft.defaultArgs
                            specialization := some sp })
    | .soft _ => .ok none
    | .hard r => .hard r
  | _, _ => .ok none

theorem generate_go_cons (env : Env) (args : List CallArg) (explicit : List Ty) (d : Decl)
    (ds : List Decl) (i : Nat) :
    generate.go env args explicit (d :: ds) i false =
      (contribution env args explicit d i).bind fun o =>
        (generate.go env args explicit ds (i + 1) false).bind fun rest => .ok (o.toList ++ rest) := by
  cases d with
  | function n ps =>
    simp only [generate.go, contribution, Subst.bind_eq, Subst.bind_ok, Subst.pure_eq]
    cases generate.go env args explicit ds (i + 1) false <;> rfl
  | functionTemplate ft =>
    simp only [generate.go, contribution, Bool.false_eq_true, ↓reduceIte]
    cases deduceTemplate env ft explicit args with
    | ok sp =>
      simp only [Subst.bind_eq, Subst.bind_ok, Subst.pure_eq]
      cases generate.go env args explicit ds (i + 1) false <;> rfl
    | soft _ =>
      simp only [Subst.bind_ok]
      cases generate.go env args explicit ds (i + 1) false <;> rfl
    | hard _ => rfl
  | _ =>
    simp only [generate.go, contribution, Subst.bind_ok]
    cases generate.go env args explicit ds (i + 1) false <;> rfl

theorem contribution_index (env : Env) (args : List CallArg) (explicit : List Ty) (d : Decl)
    (i : Nat) (c : Candidate) (h : contribution env args explicit d i = .ok (some c)) :
    c.index = i := by
  cases d with
  | function n ps => simp only [contribution, Subst.ok.injEq, Option.some.injEq] at h; rw [← h]
  | functionTemplate ft =>
    simp only [contribution] at h
    split at h
    · simp only [Subst.ok.injEq, Option.some.injEq] at h; rw [← h]
    · cases h
    · cases h
  | _ => simp [contribution] at h

/-- Two declaration lists whose contributions agree, position by
position, up to relabelling the candidates with `g`. -/
inductive ContribRel (env : Env) (args : List CallArg) (explicit : List Ty)
    (g : Candidate → Candidate) : Nat → List Decl → List Decl → Prop where
  | nil (i : Nat) : ContribRel env args explicit g i [] []
  | cons {i : Nat} {d₁ d₂ : Decl} {ds₁ ds₂ : List Decl} :
      contribution env args explicit d₂ i = (contribution env args explicit d₁ i).map (Option.map g) →
      ContribRel env args explicit g (i + 1) ds₁ ds₂ →
      ContribRel env args explicit g i (d₁ :: ds₁) (d₂ :: ds₂)

theorem generate_go_relabel (env : Env) (args : List CallArg) (explicit : List Ty)
    (g : Candidate → Candidate) {i : Nat} {ds₁ ds₂ : List Decl}
    (h : ContribRel env args explicit g i ds₁ ds₂) :
    generate.go env args explicit ds₂ i false = (generate.go env args explicit ds₁ i false).map (List.map g) := by
  induction h with
  | nil => rfl
  | cons hc _ ih =>
    rw [generate_go_cons, generate_go_cons, hc, ih]
    rename_i i d₁ d₂ ds₁ ds₂ _
    cases contribution env args explicit d₁ i with
    | ok o =>
      cases generate.go env args explicit ds₁ (i + 1) false with
      | ok rest => cases o <;> rfl
      | soft _ => rfl
      | hard _ => rfl
    | soft _ => rfl
    | hard _ => rfl

/-- A declaration list is related to itself when `g` leaves every
candidate it can contribute alone. -/
theorem contribRel_refl (env : Env) (args : List CallArg) (explicit : List Ty)
    (g : Candidate → Candidate) :
    ∀ (ds : List Decl) (j : Nat), (∀ c, j ≤ c.index → g c = c) →
      ContribRel env args explicit g j ds ds := by
  intro ds
  induction ds with
  | nil => intro j _; exact .nil j
  | cons d ds ih =>
    intro j hg
    refine .cons ?_ (ih (j + 1) (fun c hc => hg c (by omega)))
    cases hcd : contribution env args explicit d j with
    | ok o =>
      cases o with
      | none => rfl
      | some c =>
        have := contribution_index env args explicit d j c hcd
        simp only [Subst.map, Option.map_some, hg c (by omega)]
    | soft _ => rfl
    | hard _ => rfl

/-- Replacing one declaration by another whose contribution is the old
one's relabelled, where `g` touches only candidates at that position. -/
theorem contribRel_set (env : Env) (args : List CallArg) (explicit : List Ty)
    (g : Candidate → Candidate) :
    ∀ (ds : List Decl) (i k : Nat) (d₀ d' : Decl), ds[k]? = some d₀ →
      contribution env args explicit d' (i + k) =
        (contribution env args explicit d₀ (i + k)).map (Option.map g) →
      (∀ c, c.index ≠ i + k → g c = c) →
      ContribRel env args explicit g i ds (ds.set k d') := by
  intro ds
  induction ds with
  | nil => intro i k d₀ d' h; cases h
  | cons d ds ih =>
    intro i k d₀ d' hk hc hg
    have same : ∀ (d : Decl) (j : Nat), j ≠ i + k →
        contribution env args explicit d j = (contribution env args explicit d j).map (Option.map g) := by
      intro d j hj
      cases hcd : contribution env args explicit d j with
      | ok o =>
        cases o with
        | none => rfl
        | some c =>
          have := contribution_index env args explicit d j c hcd
          simp only [Subst.map, Option.map_some, hg c (by omega)]
      | soft _ => rfl
      | hard _ => rfl
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      simp only [List.set_cons_zero]
      exact .cons (by simpa using hc)
        (contribRel_refl env args explicit g ds (i + 1) (fun c hc' => hg c (by omega)))
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      simp only [List.set_cons_succ]
      exact .cons (same d i (by omega)) (ih (i + 1) k d₀ d' hk (by rw [show i + 1 + k = i + (k + 1) by omega]; exact hc)
        (fun c hc' => hg c (by omega)))

/-! ## Resolution cannot see a relabelling that keeps what it reads -/

/-- Partial ordering between two candidates, as the best viable function
consults it. -/
def orderedC (ms : Specialization → Specialization → Bool) (c₁ c₂ : Candidate) : Bool :=
  match c₁.specialization, c₂.specialization with
  | some s₁, some s₂ => ms s₁ s₂
  | _, _ => false

/-- A relabelling of candidates that keeps everything resolution reads,
except partial ordering, which is a separate hypothesis. -/
structure Keeps (g : Candidate → Candidate) : Prop where
  index : ∀ c, (g c).index = c.index
  params : ∀ c, (g c).params = c.params
  defaultArgs : ∀ c, (g c).defaultArgs = c.defaultArgs
  isTemplate : ∀ c, (g c).isTemplate = c.isTemplate

/-- Relabel a viable function's candidate. -/
def Viable.relabel (g : Candidate → Candidate) (v : Viable Conv) : Viable Conv :=
  { cand := g v.cand, convs := v.convs }

theorem viable_go_map (r : Ranking Conv) (args : List CallArg) (g : Candidate → Candidate)
    (hg : Keeps g) :
    ∀ cs, viable.go r args (cs.map g) = (viable.go r args cs).map (List.map (Viable.relabel g)) := by
  intro cs
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have ha : arityOk (g c) args.length = arityOk c args.length := by
      simp only [arityOk, hg.params, hg.defaultArgs]
    simp only [List.map_cons, viable.go, ha, hg.params]
    cases arityOk c args.length
    · simpa using ih
    · simp only [↓reduceIte]
      cases conversions r args c.params with
      | ok o =>
        cases o with
        | some convs =>
          simp only [Subst.bind_eq, Subst.bind_ok, ih]
          cases viable.go r args cs <;> rfl
        | none => simp only [Subst.bind_eq, Subst.bind_ok, ih]
      | soft _ => rfl
      | hard _ => rfl

theorem betterFunction_relabel (r : Ranking Conv) (ms : Specialization → Specialization → Bool)
    (g : Candidate → Candidate) (hg : Keeps g) (f₁ f₂ : Viable Conv)
    (ho : orderedC ms (g f₁.cand) (g f₂.cand) = orderedC ms f₁.cand f₂.cand) :
    betterFunction r ms (f₁.relabel g) (f₂.relabel g) = betterFunction r ms f₁ f₂ := by
  have e : ∀ f₁ f₂ : Viable Conv, betterFunction r ms f₁ f₂ =
      (((f₁.convs.zip f₂.convs).all fun (c₁, c₂) => !r.better c₂ c₁) &&
        (((f₁.convs.zip f₂.convs).any fun (c₁, c₂) => r.better c₁ c₂) ||
          (!f₁.cand.isTemplate && f₂.cand.isTemplate) || orderedC ms f₁.cand f₂.cand)) :=
    fun _ _ => rfl
  rw [e, e]
  simp only [Viable.relabel, hg.isTemplate, ho]

private theorem all_congr_in {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem bestViable_relabel (r : Ranking Conv) (ms : Specialization → Specialization → Bool)
    (g : Candidate → Candidate) (hg : Keeps g) (vs : List (Viable Conv))
    (ho : ∀ w ∈ vs, ∀ f ∈ vs, orderedC ms (g w.cand) (g f.cand) = orderedC ms w.cand f.cand) :
    bestViable r ms (vs.map (Viable.relabel g)) = (bestViable r ms vs).map g := by
  have hf : (vs.map (Viable.relabel g)).filter (fun w => (vs.map (Viable.relabel g)).all fun f =>
        f.cand.index == w.cand.index || betterFunction r ms w f) =
      (vs.filter fun w => vs.all fun f => f.cand.index == w.cand.index || betterFunction r ms w f).map
        (Viable.relabel g) := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro w hw
    simp only [Function.comp, List.all_map]
    apply all_congr_in
    intro f hf
    simp only [Function.comp, Viable.relabel, hg.index]
    rw [show ({ cand := g w.cand, convs := w.convs } : Viable Conv) = w.relabel g from rfl,
      show ({ cand := g f.cand, convs := f.convs } : Viable Conv) = f.relabel g from rfl,
      betterFunction_relabel r ms g hg w f (ho w hw f hf)]
  unfold bestViable
  cases vs with
  | nil => rfl
  | cons v vs' =>
    simp only [List.map_cons]
    rw [show (Viable.relabel g v :: vs'.map (Viable.relabel g)) = (v :: vs').map (Viable.relabel g) from rfl, hf]
    generalize (v :: vs').filter (fun w => (v :: vs').all fun f =>
      f.cand.index == w.cand.index || betterFunction r ms w f) = best
    cases best with
    | nil => simp [Resolution.map, Viable.relabel]
    | cons w ws =>
      cases ws with
      | nil => rfl
      | cons w' ws => simp [Resolution.map, Viable.relabel]

/-- Resolution of two declaration lists whose candidates differ by a
relabelling that keeps what resolution reads, and partial ordering among
the candidates generated, is the same resolution relabelled. -/
theorem resolve_relabel (env : Env) (r : Ranking Conv) (decls₁ decls₂ : List Decl)
    (args : List CallArg) (explicit : List Ty) (g : Candidate → Candidate) (hg : Keeps g)
    (h : generate .text env decls₂ args explicit =
      (generate .text env decls₁ args explicit).map (List.map g))
    (ho : ∀ cs, generate .text env decls₁ args explicit = .ok cs →
      ∀ c₁ ∈ cs, ∀ c₂ ∈ cs, orderedC (orderingForCall args.length) (g c₁) (g c₂) =
        orderedC (orderingForCall args.length) c₁ c₂) :
    resolve .text env r decls₂ args explicit = (resolve .text env r decls₁ args explicit).map g := by
  unfold resolve
  rw [h]
  cases hgen : generate .text env decls₁ args explicit with
  | ok cs =>
    simp only [Subst.map, viable]
    rw [viable_go_map r args g hg cs]
    cases hv : viable.go r args cs with
    | ok vs =>
      simp only [Subst.map]
      apply bestViable_relabel r _ g hg vs
      have hsub := viable_go_sublist r args cs vs hv
      intro w hw f hf
      exact ho cs hgen w.cand (hsub.subset (List.mem_map_of_mem hw))
        f.cand (hsub.subset (List.mem_map_of_mem hf))
    | soft _ => rfl
    | hard _ => rfl
  | soft _ => rfl
  | hard _ => rfl

theorem resolution_map_index (x : Resolution Candidate) (g : Candidate → Candidate)
    (hg : ∀ c, (g c).index = c.index) :
    (x.map g).map (·.index) = x.map (·.index) := by
  cases x <;> simp [Resolution.map, hg]

theorem subst_map_id (x : Subst α) : x.map id = x := by cases x <;> rfl

theorem deduceTemplate_template (env : Env) (ft : FunctionTemplate) (explicit : List Ty)
    (args : List CallArg) (sp : Specialization) (h : deduceTemplate env ft explicit args = .ok sp) :
    sp.template = ft := by
  unfold deduceTemplate at h
  generalize explicitStep ft.head explicit >>= callStep env ft.params args >>= defaultsStep env ft.head
    >>= parameterListStep env ft.head >>= constraintStep env ft.constraint
    >>= nonDependentStep env ft.params args = pre at h
  cases pre with
  | ok σ =>
    simp only [Subst.bind_eq, Subst.bind_ok, functionTypeStep] at h
    cases hp : formAll env (ft.params.map (Ty.subst σ)) with
    | ok ps =>
      rw [hp] at h
      simp only [Subst.bind_ok] at h
      cases hr : form env (ft.ret.subst σ) with
      | ok t => rw [hr] at h; simp only [Subst.bind_ok, Subst.pure_eq, Subst.ok.injEq] at h; rw [← h]
      | soft _ => rw [hr] at h; cases h
      | hard _ => rw [hr] at h; cases h
    | soft _ => rw [hp] at h; cases h
    | hard _ => rw [hp] at h; cases h
  | soft _ => cases h
  | hard _ => cases h

/-- Each generated candidate is the contribution of the declaration at
its position. -/
theorem generate_go_mem (env : Env) (args : List CallArg) (explicit : List Ty) :
    ∀ (ds : List Decl) (i : Nat) (cs : List Candidate), generate.go env args explicit ds i false = .ok cs →
      ∀ c ∈ cs, ∃ j d, ds[j]? = some d ∧ contribution env args explicit d (i + j) = .ok (some c) := by
  intro ds
  induction ds with
  | nil => intro i cs h; cases h; intro c hc; cases hc
  | cons d ds ih =>
    intro i cs h c hc
    rw [generate_go_cons] at h
    cases hd : contribution env args explicit d i with
    | ok o =>
      rw [hd] at h
      simp only [Subst.bind_ok] at h
      cases hg : generate.go env args explicit ds (i + 1) false with
      | ok rest =>
        rw [hg] at h
        simp only [Subst.bind_ok, Subst.ok.injEq] at h
        subst h
        rcases List.mem_append.mp hc with hc | hc
        · cases o with
          | none => cases hc
          | some c' =>
            simp only [Option.toList_some, List.mem_singleton] at hc
            subst hc
            exact ⟨0, d, rfl, by simpa using hd⟩
        · obtain ⟨j, d', hj, hc'⟩ := ih (i + 1) rest hg c hc
          exact ⟨j + 1, d', by simpa using hj, by rw [show i + (j + 1) = i + 1 + j by omega]; exact hc'⟩
      | soft _ => rw [hg] at h; cases h
      | hard _ => rw [hg] at h; cases h
    | soft _ => rw [hd] at h; cases h
    | hard _ => rw [hd] at h; cases h

theorem generate_text (env : Env) (decls : List Decl) (args : List CallArg) (explicit : List Ty) :
    generate .text env decls args explicit = generate.go env args explicit decls 0 false := by
  simp [generate]

/-- The candidate a call generates at a template's position has that
template. -/
theorem generated_template (env : Env) (decls : List Decl) (args : List CallArg) (explicit : List Ty)
    (k : Nat) (ft : FunctionTemplate) (hk : decls[k]? = some (.functionTemplate ft))
    (cs : List Candidate) (h : generate .text env decls args explicit = .ok cs) (c : Candidate)
    (hc : c ∈ cs) (hi : c.index = k) (sp : Specialization) (hs : c.specialization = some sp) :
    sp.template = ft := by
  rw [generate_text] at h
  obtain ⟨j, d, hj, hcd⟩ := generate_go_mem env args explicit decls 0 cs h c hc
  have := contribution_index env args explicit d (0 + j) c hcd
  have hjk : j = k := by omega
  subst hjk
  rw [hk] at hj
  cases hj
  simp only [contribution, Nat.zero_add] at hcd
  cases hd : deduceTemplate env ft explicit args with
  | ok sp' =>
    rw [hd] at hcd
    simp only [Subst.ok.injEq, Option.some.injEq] at hcd
    rw [← hcd] at hs
    simp only [Option.some.injEq] at hs
    rw [← hs]
    exact deduceTemplate_template env ft explicit args _ hd
  | soft _ => rw [hd] at hcd; cases hcd
  | hard _ => rw [hd] at hcd; cases hcd

/-! ## The Mandates of the selected function -/

/-- The selected specialization's Mandates, checked once overload
resolution has selected it: an unmet Mandate makes the program
ill-formed. -/
@[std rule "structure.specifications#3"]
def mandateCheck (env : Env) (c : Candidate) : Subst Bool :=
  match c.specialization with
  | some sp =>
    match sp.template.mandate with
    | some m => Constraint.satisfied env.atomic sp.args m
    | none => .ok true
  | none => .ok true

/-- An evaluated call: overload resolution, then the selected function's
Mandates, as its definition is instantiated. -/
def invoke (mode : Mode) (env : Env) (r : Ranking Conv) (decls : List Decl) (args : List CallArg)
    (explicit : List Ty := []) : Resolution Candidate :=
  match resolve mode env r decls args explicit with
  | .selected c =>
    match mandateCheck env c with
    | .ok true => .selected c
    | .ok false => .illFormed "a Mandate of the selected function is not met"
    | .soft e | .hard e => .illFormed e
  | o => o

/-- At the call, a Mandate only turns a selection into an ill-formed
program: what the call selects, resolution selected. -/
theorem invoke_selected (mode : Mode) (env : Env) (r : Ranking Conv) (decls : List Decl)
    (args : List CallArg) (explicit : List Ty) (c : Candidate)
    (h : invoke mode env r decls args explicit = .selected c) :
    resolve mode env r decls args explicit = .selected c := by
  unfold invoke at h
  split at h
  · split at h
    · exact h ▸ by assumption
    all_goals cases h
  · exact h

theorem invoke_of_selected (mode : Mode) (env : Env) (r : Ranking Conv) (decls : List Decl)
    (args : List CallArg) (explicit : List Ty) (c : Candidate)
    (h : resolve mode env r decls args explicit = .selected c) :
    invoke mode env r decls args explicit = .selected c ∨
      ∃ e, invoke mode env r decls args explicit = .illFormed e := by
  unfold invoke
  rw [h]
  simp only
  split
  · exact .inl rfl
  · exact .inr ⟨_, rfl⟩
  · exact .inr ⟨_, rfl⟩
  · exact .inr ⟨_, rfl⟩

theorem invoke_of_not_selected (mode : Mode) (env : Env) (r : Ranking Conv) (decls : List Decl)
    (args : List CallArg) (explicit : List Ty)
    (h : ∀ c, resolve mode env r decls args explicit ≠ .selected c) :
    invoke mode env r decls args explicit = resolve mode env r decls args explicit := by
  unfold invoke
  split
  · rename_i c hc; exact absurd hc (h c)
  · rfl

/-! ## mandate-inertness -/

/-- Give the candidate at position `k` the Mandates `m`. -/
def withMandateAt (k : Nat) (m : Option Constraint) (c : Candidate) : Candidate :=
  if c.index = k then
    { c with specialization := c.specialization.map fun sp => { sp with template := { sp.template with mandate := m } } }
  else c

theorem keeps_withMandateAt (k : Nat) (m : Option Constraint) : Keeps (withMandateAt k m) where
  index c := by unfold withMandateAt; split <;> rfl
  params c := by unfold withMandateAt; split <;> rfl
  defaultArgs c := by unfold withMandateAt; split <;> rfl
  isTemplate c := by
    unfold withMandateAt Candidate.isTemplate
    split
    · cases c.specialization <;> rfl
    · rfl

/-- Partial ordering does not read the Mandates. -/
theorem orderedC_withMandateAt (n k : Nat) (m : Option Constraint) (c₁ c₂ : Candidate) :
    orderedC (orderingForCall n) (withMandateAt k m c₁) (withMandateAt k m c₂) =
      orderedC (orderingForCall n) c₁ c₂ := by
  unfold withMandateAt orderedC
  by_cases h₁ : c₁.index = k <;> by_cases h₂ : c₂.index = k <;>
    simp only [h₁, h₂, ↓reduceIte] <;>
    cases c₁.specialization <;> cases c₂.specialization <;> rfl

theorem contribution_mandate (env : Env) (args : List CallArg) (explicit : List Ty)
    (ft : FunctionTemplate) (m : Option Constraint) (k : Nat) :
    contribution env args explicit (.functionTemplate { ft with mandate := m }) k =
      (contribution env args explicit (.functionTemplate ft) k).map (Option.map (withMandateAt k m)) := by
  simp only [contribution, deduceTemplate_mandate]
  cases hd : deduceTemplate env ft explicit args with
  | ok sp =>
    have ht := deduceTemplate_template env ft explicit args sp hd
    simp only [Subst.map, Option.map_some, withMandateAt, ↓reduceIte, Option.map_some,
      Specialization.withTemplate, ht]
  | soft _ => rfl
  | hard _ => rfl

/-- mandate-inertness: giving a function template Mandates does not
change overload resolution. The same candidates are viable and the same
one is selected, which differs only in carrying the Mandates. -/
theorem mandate_inertness (env : Env) (r : Ranking Conv) (decls : List Decl) (args : List CallArg)
    (explicit : List Ty) (k : Nat) (ft : FunctionTemplate) (m : Option Constraint)
    (hk : decls[k]? = some (.functionTemplate ft)) :
    resolve .text env r (decls.set k (.functionTemplate { ft with mandate := m })) args explicit =
      (resolve .text env r decls args explicit).map (withMandateAt k m) := by
  apply resolve_relabel env r decls _ args explicit _ (keeps_withMandateAt k m)
  · rw [generate_text, generate_text]
    apply generate_go_relabel
    apply contribRel_set env args explicit _ decls 0 k _ _ hk
    · simpa using contribution_mandate env args explicit ft m k
    · intro c hc; unfold withMandateAt; simp [show c.index ≠ k by omega]
  · intro _ _ c₁ _ c₂ _
    exact orderedC_withMandateAt _ k m c₁ c₂

/-- The same, as which candidate is selected. -/
theorem mandate_inertness_index (env : Env) (r : Ranking Conv) (decls : List Decl)
    (args : List CallArg) (explicit : List Ty) (k : Nat) (ft : FunctionTemplate)
    (m : Option Constraint) (hk : decls[k]? = some (.functionTemplate ft)) :
    (resolve .text env r (decls.set k (.functionTemplate { ft with mandate := m })) args explicit).map
        (·.index) = (resolve .text env r decls args explicit).map (·.index) := by
  rw [mandate_inertness env r decls args explicit k ft m hk]
  exact resolution_map_index _ _ (keeps_withMandateAt k m).index

/-! ## constraint-promotion -/

/-- Turn a function template's Mandates into a constraint, conjoined after
its associated constraints. -/
def promote (ft : FunctionTemplate) : FunctionTemplate :=
  match ft.mandate with
  | none => ft
  | some m =>
    { ft with
      constraint := some (match ft.constraint with
        | some c => .conj c m
        | none => m)
      mandate := none }

private theorem functionTypeStep_relabel (env : Env) (ft ft' : FunctionTemplate)
    (hp : ft'.params = ft.params) (hr : ft'.ret = ft.ret) (σ : Bindings) :
    functionTypeStep env ft' σ = (functionTypeStep env ft σ).map (Specialization.withTemplate ft') := by
  simp only [functionTypeStep, hp, hr]
  cases formAll env (ft.params.map (Ty.subst σ)) with
  | ok ps =>
    simp only [Subst.bind_eq, Subst.bind_ok]
    cases form env (ft.ret.subst σ) <;> rfl
  | soft _ => rfl
  | hard _ => rfl

private theorem bind_map_relabel (x : Subst Bindings) (f : Bindings → Subst Specialization)
    (f' : Bindings → Subst Specialization) (g : Specialization → Specialization)
    (h : ∀ σ, f' σ = (f σ).map g) : (x >>= f') = (x >>= f).map g := by
  cases x with
  | ok σ => exact h σ
  | soft _ => rfl
  | hard _ => rfl

/-- Deducing the promoted template: the same deduction relabelled, or a
deduction failure where the promoted Mandate is not met. A hard error in
checking the Mandate is excluded by hypothesis: promoted, it would make
every call that deduces the template ill-formed. -/
theorem deduceTemplate_promote (env : Env) (ft : FunctionTemplate) (m : Constraint)
    (explicit : List Ty) (args : List CallArg) (hm : ft.mandate = some m)
    (hno : ∀ σ e, Constraint.satisfied env.atomic σ m ≠ .hard e) :
    deduceTemplate env (promote ft) explicit args =
        (deduceTemplate env ft explicit args).map (Specialization.withTemplate (promote ft)) ∨
      ∃ e, deduceTemplate env (promote ft) explicit args = .soft e := by
  have hft : promote ft = { ft with
      constraint := some (match ft.constraint with | some c => .conj c m | none => m)
      mandate := none } := by simp [promote, hm]
  have tail : ∀ σ, (nonDependentStep env ft.params args σ >>= functionTypeStep env (promote ft)) =
      (nonDependentStep env ft.params args σ >>= functionTypeStep env ft).map
        (Specialization.withTemplate (promote ft)) := by
    intro σ
    exact bind_map_relabel _ _ _ _ (functionTypeStep_relabel env ft (promote ft)
      (by rw [hft]) (by rw [hft]))
  unfold deduceTemplate
  rw [show (promote ft).head = ft.head by rw [hft], show (promote ft).params = ft.params by rw [hft]]
  generalize explicitStep ft.head explicit >>= callStep env ft.params args >>= defaultsStep env ft.head
    >>= parameterListStep env ft.head = pre
  cases pre with
  | soft _ => exact .inl rfl
  | hard _ => exact .inl rfl
  | ok σ =>
    simp only [Subst.bind_eq, Subst.bind_ok]
    rw [show (promote ft).constraint = some (match ft.constraint with | some c => .conj c m | none => m)
      by rw [hft]]
    have hrest := tail σ
    simp only [Subst.bind_eq] at hrest
    cases hc : ft.constraint with
    | none =>
      simp only [constraintStep, Subst.bind_eq]
      cases hs : Constraint.satisfied env.atomic σ m with
      | ok b =>
        cases b with
        | true =>
          left
          simp only [Subst.bind_ok, ↓reduceIte, Subst.pure_eq]
          exact hrest
        | false => right; exact ⟨_, rfl⟩
      | soft _ => right; exact ⟨_, rfl⟩
      | hard e => exact absurd hs (hno σ e)
    | some c =>
      simp only [constraintStep, Subst.bind_eq, Constraint.satisfied]
      cases hsc : Constraint.satisfied env.atomic σ c with
      | ok b =>
        cases b with
        | true =>
          simp only [Subst.bind_ok, ↓reduceIte]
          cases hs : Constraint.satisfied env.atomic σ m with
          | ok b' =>
            cases b' with
            | true =>
              left
              simp only [Subst.bind_ok, ↓reduceIte, Subst.pure_eq]
              exact hrest
            | false => right; exact ⟨_, rfl⟩
          | soft _ => right; exact ⟨_, rfl⟩
          | hard e => exact absurd hs (hno σ e)
        | false => left; rfl
      | soft _ => left; rfl
      | hard _ => left; rfl

theorem promote_defaultArgs (ft : FunctionTemplate) : (promote ft).defaultArgs = ft.defaultArgs := by
  unfold promote; split <;> rfl

/-- Give the candidate at position `k` the promoted template. -/
def promoteAt (k : Nat) (ft : FunctionTemplate) (c : Candidate) : Candidate :=
  if c.index = k then
    { c with specialization := c.specialization.map (Specialization.withTemplate (promote ft)) }
  else c

theorem keeps_promoteAt (k : Nat) (ft : FunctionTemplate) : Keeps (promoteAt k ft) where
  index c := by unfold promoteAt; split <;> rfl
  params c := by unfold promoteAt; split <;> rfl
  defaultArgs c := by unfold promoteAt; split <;> rfl
  isTemplate c := by
    unfold promoteAt Candidate.isTemplate
    split
    · cases c.specialization <;> rfl
    · rfl

/-- constraint-promotion, as far as it holds. Turning a template's
Mandates into a constraint either leaves resolution as it was, up to the
template the candidate carries, or removes the candidate: the call then
resolves as if the declaration contributed nothing. The first case needs
the promoted constraint not to change partial ordering against any
other candidate the call generates; `promotion_reorders` shows it can. -/
theorem constraint_promotion (env : Env) (r : Ranking Conv) (decls : List Decl)
    (args : List CallArg) (explicit : List Ty) (k : Nat) (ft : FunctionTemplate) (m : Constraint)
    (hk : decls[k]? = some (.functionTemplate ft)) (hm : ft.mandate = some m)
    (hno : ∀ σ e, Constraint.satisfied env.atomic σ m ≠ .hard e)
    (hord : ∀ cs, generate .text env decls args explicit = .ok cs → ∀ c ∈ cs, c.index ≠ k →
      ∀ sp, c.specialization = some sp →
        PartialOrdering.moreSpecialized (some args.length) (promote ft) sp.template =
            PartialOrdering.moreSpecialized (some args.length) ft sp.template ∧
          PartialOrdering.moreSpecialized (some args.length) sp.template (promote ft) =
            PartialOrdering.moreSpecialized (some args.length) sp.template ft) :
    resolve .text env r (decls.set k (.functionTemplate (promote ft))) args explicit =
        (resolve .text env r decls args explicit).map (promoteAt k ft) ∨
      ∀ d, (∀ i, contribution env args explicit d i = .ok none) →
        resolve .text env r (decls.set k (.functionTemplate (promote ft))) args explicit =
          resolve .text env r (decls.set k d) args explicit := by
  rcases deduceTemplate_promote env ft m explicit args hm hno with hd | ⟨e, hd⟩
  · left
    apply resolve_relabel env r decls _ args explicit _ (keeps_promoteAt k ft)
    · rw [generate_text, generate_text]
      apply generate_go_relabel
      apply contribRel_set env args explicit _ decls 0 k _ _ hk
      · simp only [Nat.zero_add, contribution, hd]
        cases hd' : deduceTemplate env ft explicit args with
        | ok sp => simp [Subst.map, promoteAt, promote_defaultArgs, Specialization.withTemplate]
        | soft _ => rfl
        | hard _ => rfl
      · intro c hc; unfold promoteAt; simp [show c.index ≠ k by omega]
    · intro cs hcs c₁ hc₁ c₂ hc₂
      have hsorted := (generate_go_sorted env args explicit false decls 0 cs
        (by rw [← generate_text]; exact hcs)).2
      unfold orderedC promoteAt
      by_cases h₁ : c₁.index = k <;> by_cases h₂ : c₂.index = k
      · -- the same candidate
        have : c₁ = c₂ := pairwise_index_eq hsorted c₁ hc₁ c₂ hc₂ (by rw [h₁, h₂])
        subst this
        simp only [h₁, ↓reduceIte]
        cases hs : c₁.specialization with
        | none => rfl
        | some sp =>
          simp only [Option.map_some]
          show orderingForCall _ (sp.withTemplate (promote ft)) (sp.withTemplate (promote ft)) =
            orderingForCall _ sp sp
          simp only [orderingForCall, Specialization.withTemplate, PartialOrdering.moreSpecialized_irrefl]
      · simp only [h₁, h₂, ↓reduceIte]
        cases hs₁ : c₁.specialization with
        | none => rfl
        | some sp₁ =>
          cases hs₂ : c₂.specialization with
          | none => rfl
          | some sp₂ =>
            simp only [Option.map_some]
            have ht := generated_template env decls args explicit k ft hk cs hcs c₁ hc₁ h₁ sp₁ hs₁
            show PartialOrdering.moreSpecialized _ (promote ft) sp₂.template =
              PartialOrdering.moreSpecialized _ sp₁.template sp₂.template
            rw [ht]
            exact (hord cs hcs c₂ hc₂ h₂ sp₂ hs₂).1
      · simp only [h₁, h₂, ↓reduceIte]
        cases hs₁ : c₁.specialization with
        | none => rfl
        | some sp₁ =>
          cases hs₂ : c₂.specialization with
          | none => rfl
          | some sp₂ =>
            simp only [Option.map_some]
            have ht := generated_template env decls args explicit k ft hk cs hcs c₂ hc₂ h₂ sp₂ hs₂
            show PartialOrdering.moreSpecialized _ sp₁.template (promote ft) =
              PartialOrdering.moreSpecialized _ sp₁.template sp₂.template
            rw [ht]
            exact (hord cs hcs c₁ hc₁ h₁ sp₁ hs₁).2
      · simp only [h₁, h₂, ↓reduceIte]
  · right
    intro d hnone
    have hset : (decls.set k d).set k (.functionTemplate (promote ft)) =
        decls.set k (.functionTemplate (promote ft)) := by simp
    have hk' : (decls.set k d)[k]? = some d := by
      simp [(List.getElem?_eq_some_iff.mp hk).1]
    have hrel := contribRel_set env args explicit id (decls.set k d) 0 k d
      (.functionTemplate (promote ft)) hk'
      (by rw [hnone]; simp only [contribution, hd]; rfl) (fun _ _ => rfl)
    rw [hset] at hrel
    have hgen := generate_go_relabel env args explicit id hrel
    simp only [List.map_id_fun, subst_map_id] at hgen
    unfold resolve
    rw [generate_text, generate_text, hgen]

/-! ## Promotion can reorder -/

private def T : Ty := .param 0

/-- Two templates for one call. The first requires `class_like`. The
second is unconstrained, with the Mandate `empty_like`. -/
def promotionProgram (promoted : Bool) : Program :=
  let second : FunctionTemplate :=
    { name := "g", head := [{ kind := .type }], params := [T]
      mandate := some (.atomic "empty_like" [T]) }
  [ .class "X", .concept "class_like" "std::is_class_v<T>", .concept "empty_like" "std::is_empty_v<T>"
  , .functionTemplate { name := "g", head := [{ kind := .type }], params := [T]
                        constraint := some (.atomic "class_like" [T]) }
  , .functionTemplate (if promoted then promote second else second) ]

/-- Both conditions hold for `X`. -/
def promotionAtomics : List (String × List Ty × Bool) :=
  [("class_like", [.named "X"], true), ("empty_like", [.named "X"], true)]

/-- constraint-promotion fails as the plan stated it. Before promotion
the first template is more constrained and is selected; removing the
second changes nothing. Promoted, the second template's constraint is
neither subsumed by nor subsumes the first's, so the call is ambiguous:
an outcome neither the old resolution nor removal gives. -/
theorem promotion_reorders :
    let call := fun p => (invoke .text (Env.ofProgram p promotionAtomics) p.ranking
      (p.candidates "g") [{ ty := .named "X" }]).map (·.index)
    call (promotionProgram false) = .selected 0 ∧
      call ((promotionProgram false).set 4 (.concept "removed" "true")) = .selected 0 ∧
      call (promotionProgram true) = .ambiguous [0, 1] := by
  refine ⟨rfl, rfl, rfl⟩

end Overload
