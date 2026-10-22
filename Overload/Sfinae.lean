-- Overload/Sfinae.lean                                               -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Mandates

/-!
# sfinae-requires

The plan's sfinae-requires target: an `enable_if` encoding and a
requires-clause with the same condition give the same viable set, and
differ only where ordering consults subsumption.

The encoding modelled is return-type SFINAE, `auto f(T) ->
std::enable_if_t<C<T>, R>`, which keeps the template head the requires
form has. The two forms check the condition at different steps of
[temp.deduct.general]/5: the requires-clause before convertibility and
the function type, `enable_if` while the function type is substituted.
So the theorem (`sfinae_requires`) needs those later steps, and the
condition itself, not to fail hard. Where they can, the requires-clause
shields the call and `enable_if` does not (`sfinae_unshielded`).

Given that, the candidates are the same up to the template each carries,
so the viable functions are the same, and resolution is the same where
partial ordering against the other candidates does not change. Where it
does, a requires-clause wins by subsumption and `enable_if` does not
(`sfinae_loses_subsumption`).
-/

namespace Overload

/-- The requires-clause encoding of the condition `c<m>`. -/
def requiresForm (ft : FunctionTemplate) (c : String) (m : List Ty) : FunctionTemplate :=
  { ft with constraint := some (.atomic c m) }

/-- The `enable_if` encoding of the condition `c<m>`, in the return
type. -/
def enableIfForm (ft : FunctionTemplate) (c : String) (m : List Ty) : FunctionTemplate :=
  { ft with ret := .enableIf c (Ty.args m) ft.ret }

/-- Two outcomes that are equal, or both deduction failures, whatever
their reasons. Candidate generation does not read the reason of a
deduction failure. -/
def SameUpToSoft (x y : Subst α) : Prop :=
  x = y ∨ ∃ r₁ r₂, x = .soft r₁ ∧ y = .soft r₂

theorem subst_args (σ : Bindings) : ∀ m : List Ty, Ty.subst σ (Ty.args m) = Ty.args (m.map (Ty.subst σ))
  | [] => rfl
  | t :: ts => by simp only [Ty.args, Ty.subst, List.map_cons, subst_args σ ts]

theorem toList_args : ∀ m : List Ty, (Ty.args m).toList = some m
  | [] => rfl
  | t :: ts => by simp only [Ty.args, Ty.toList, toList_args ts, Option.map_some]

private theorem functionTypeStep_enableIf (env : Env) (ft : FunctionTemplate) (c : String)
    (m : List Ty) (σ : Bindings) :
    functionTypeStep env (enableIfForm ft c m) σ =
      ((formAll env (ft.params.map (Ty.subst σ))).bind fun ps =>
        (form env (ft.ret.subst σ)).bind fun t =>
          match env.atomic c (m.map (Ty.subst σ)) with
          | .ok true => .ok { template := enableIfForm ft c m, args := σ, params := ps, ret := t }
          | .ok false => .soft s!"enable_if condition {c} is false"
          | .soft r => .soft r
          | .hard r => .hard r) := by
  simp only [functionTypeStep, enableIfForm, Ty.subst, form, subst_args, toList_args,
    Option.getD_some, Subst.bind_eq, Subst.pure_eq]
  cases formAll env (ft.params.map (Ty.subst σ)) with
  | ok ps =>
    simp only [Subst.bind_ok]
    cases form env (ft.ret.subst σ) with
    | ok t =>
      simp only [Subst.bind_ok]
      cases env.atomic c (m.map (Ty.subst σ)) with
      | ok b => cases b <;> rfl
      | soft _ => rfl
      | hard _ => rfl
    | soft _ => rfl
    | hard _ => rfl
  | soft _ => rfl
  | hard _ => rfl

/-- Deducing the `enable_if` form is deducing the requires form, up to
the template and the reason of a failure, provided the condition, the
convertibility check and the function type never fail hard. -/
theorem deduceTemplate_enableIf (env : Env) (ft : FunctionTemplate) (c : String) (m : List Ty)
    (explicit : List Ty) (args : List CallArg) (hcon : ft.constraint = none)
    (hq : ∀ σ e, env.atomic c (m.map (Ty.subst σ)) ≠ .hard e)
    (hnd : ∀ σ e, nonDependentStep env ft.params args σ ≠ .hard e)
    (hfp : ∀ σ e, formAll env (ft.params.map (Ty.subst σ)) ≠ .hard e)
    (hfr : ∀ σ e, form env (ft.ret.subst σ) ≠ .hard e) :
    SameUpToSoft (deduceTemplate env (enableIfForm ft c m) explicit args)
      ((deduceTemplate env (requiresForm ft c m) explicit args).map
        (Specialization.withTemplate (enableIfForm ft c m))) := by
  unfold deduceTemplate
  have hS : (enableIfForm ft c m).constraint = none := hcon
  rw [show (enableIfForm ft c m).head = ft.head from rfl, show (enableIfForm ft c m).params = ft.params from rfl,
    show (requiresForm ft c m).head = ft.head from rfl, show (requiresForm ft c m).params = ft.params from rfl,
    show (requiresForm ft c m).constraint = some (.atomic c m) from rfl, hS]
  generalize explicitStep env ft.head explicit >>= callStep env ft.params args >>= defaultsStep env ft.head
    >>= parameterListStep env ft.head = pre
  cases pre with
  | soft _ => exact .inl rfl
  | hard _ => exact .inl rfl
  | ok σ =>
    simp only [Subst.bind_eq, Subst.bind_ok, constraintStep, Constraint.satisfied]
    have hfS := functionTypeStep_enableIf env ft c m σ
    cases hN : nonDependentStep env ft.params args σ with
    | hard e => exact absurd hN (hnd σ e)
    | soft r =>
      cases hqσ : env.atomic c (m.map (Ty.subst σ)) with
      | hard e => exact absurd hqσ (hq σ e)
      | soft _ => exact .inr ⟨_, _, rfl, rfl⟩
      | ok b =>
        cases b with
        | true => left; simp [hN]; rfl
        | false => exact .inr ⟨_, _, rfl, rfl⟩
    | ok σ' =>
      have hσ := nonDependentStep_ok env ft.params args σ σ' hN
      subst hσ
      simp only [Subst.bind_ok, hfS]
      cases hP : formAll env (ft.params.map (Ty.subst σ')) with
      | hard e => exact absurd hP (hfp σ' e)
      | soft r =>
        cases hqσ : env.atomic c (m.map (Ty.subst σ')) with
        | hard e => exact absurd hqσ (hq σ' e)
        | soft _ => exact .inr ⟨_, _, rfl, rfl⟩
        | ok b =>
          cases b with
          | true => left; simp [hN, functionTypeStep, requiresForm, hP, Subst.map]
          | false => exact .inr ⟨_, _, rfl, rfl⟩
      | ok ps =>
        cases hR : form env (ft.ret.subst σ') with
        | hard e => exact absurd hR (hfr σ' e)
        | soft r =>
          cases hqσ : env.atomic c (m.map (Ty.subst σ')) with
          | hard e => exact absurd hqσ (hq σ' e)
          | soft _ => exact .inr ⟨_, _, rfl, rfl⟩
          | ok b =>
            cases b with
            | true => left; simp [hN, functionTypeStep, hP, requiresForm, hR]; rfl
            | false => exact .inr ⟨_, _, rfl, rfl⟩
        | ok t =>
          cases hqσ : env.atomic c (m.map (Ty.subst σ')) with
          | hard e => exact absurd hqσ (hq σ' e)
          | soft _ => exact .inr ⟨_, _, rfl, rfl⟩
          | ok b =>
            cases b with
            | true =>
              left
              simp [hN, functionTypeStep, hP, requiresForm, hR, Subst.map, Specialization.withTemplate]
            | false => exact .inr ⟨_, _, rfl, rfl⟩

/-! ## The same candidates, up to the template -/

/-- Give the candidate at position `k` the template `ft'`. -/
def templateAt (k : Nat) (ft' : FunctionTemplate) (c : Candidate) : Candidate :=
  if c.index = k then
    { c with specialization := c.specialization.map (Specialization.withTemplate ft') }
  else c

theorem keeps_templateAt (k : Nat) (ft' : FunctionTemplate) : Keeps (templateAt k ft') where
  index c := by unfold templateAt; split <;> rfl
  params c := by unfold templateAt; split <;> rfl
  defaultArgs c := by unfold templateAt; split <;> rfl
  isTemplate c := by
    unfold templateAt Candidate.isTemplate
    split
    · cases c.specialization <;> rfl
    · rfl

theorem contribution_sameUpToSoft (env : Env) (args : List CallArg) (explicit : List Ty)
    (ft₁ ft₂ : FunctionTemplate) (k : Nat) (hd : ft₂.defaultArgs = ft₁.defaultArgs)
    (h : SameUpToSoft (deduceTemplate env ft₂ explicit args)
      ((deduceTemplate env ft₁ explicit args).map (Specialization.withTemplate ft₂))) :
    contribution env args explicit (.functionTemplate ft₂) k =
      (contribution env args explicit (.functionTemplate ft₁) k).map (Option.map (templateAt k ft₂)) := by
  simp only [contribution]
  rcases h with h | ⟨r₁, r₂, h₁, h₂⟩
  · rw [h]
    cases deduceTemplate env ft₁ explicit args with
    | ok sp => simp [Subst.map, templateAt, hd, Specialization.withTemplate]
    | soft _ => rfl
    | hard _ => rfl
  · rw [h₁]
    cases h₁' : deduceTemplate env ft₁ explicit args with
    | ok sp => rw [h₁'] at h₂; cases h₂
    | soft _ => rfl
    | hard _ => rw [h₁'] at h₂; cases h₂

/-- Partial ordering among the generated candidates is unchanged by giving
the candidate at a template's position another template, when ordering
that template against each other candidate is unchanged. -/
theorem ordering_templateAt (env : Env) (decls : List Decl) (args : List CallArg)
    (explicit : List Ty) (k : Nat) (ft ft' : FunctionTemplate)
    (hk : decls[k]? = some (.functionTemplate ft))
    (hord : ∀ cs, generate .text env decls args explicit = .ok cs → ∀ c ∈ cs, c.index ≠ k →
      ∀ sp, c.specialization = some sp →
        PartialOrdering.moreSpecialized (some args.length) ft' sp.template =
            PartialOrdering.moreSpecialized (some args.length) ft sp.template ∧
          PartialOrdering.moreSpecialized (some args.length) sp.template ft' =
            PartialOrdering.moreSpecialized (some args.length) sp.template ft) :
    ∀ cs, generate .text env decls args explicit = .ok cs → ∀ c₁ ∈ cs, ∀ c₂ ∈ cs,
      orderedC (orderingForCall args.length) (templateAt k ft' c₁) (templateAt k ft' c₂) =
        orderedC (orderingForCall args.length) c₁ c₂ := by
  intro cs hcs c₁ hc₁ c₂ hc₂
  have hsorted := (generate_go_sorted env args explicit false decls 0 cs
    (by rw [← generate_text]; exact hcs)).2
  unfold orderedC templateAt
  by_cases h₁ : c₁.index = k <;> by_cases h₂ : c₂.index = k
  · have : c₁ = c₂ := pairwise_index_eq hsorted c₁ hc₁ c₂ hc₂ (by rw [h₁, h₂])
    subst this
    simp only [h₁, ↓reduceIte]
    cases c₁.specialization with
    | none => rfl
    | some sp =>
      simp only [Option.map_some]
      show orderingForCall _ (sp.withTemplate ft') (sp.withTemplate ft') = orderingForCall _ sp sp
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
        show PartialOrdering.moreSpecialized _ ft' sp₂.template =
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
        show PartialOrdering.moreSpecialized _ sp₁.template ft' =
          PartialOrdering.moreSpecialized _ sp₁.template sp₂.template
        rw [ht]
        exact (hord cs hcs c₁ hc₁ h₁ sp₁ hs₁).2
  · simp only [h₁, h₂, ↓reduceIte]

/-- sfinae-requires, for the candidates: replacing a requires-clause by
`enable_if` in the return type, with the same condition, gives the same
candidates up to the template the replaced one carries, so the same
viable functions. It needs the condition, the convertibility check and
the function type never to fail hard. -/
theorem sfinae_requires (env : Env) (decls : List Decl) (args : List CallArg) (explicit : List Ty)
    (k : Nat) (ft : FunctionTemplate) (c : String) (m : List Ty)
    (hk : decls[k]? = some (.functionTemplate (requiresForm ft c m))) (hcon : ft.constraint = none)
    (hq : ∀ σ e, env.atomic c (m.map (Ty.subst σ)) ≠ .hard e)
    (hnd : ∀ σ e, nonDependentStep env ft.params args σ ≠ .hard e)
    (hfp : ∀ σ e, formAll env (ft.params.map (Ty.subst σ)) ≠ .hard e)
    (hfr : ∀ σ e, form env (ft.ret.subst σ) ≠ .hard e) :
    generate .text env (decls.set k (.functionTemplate (enableIfForm ft c m))) args explicit =
      (generate .text env decls args explicit).map (List.map (templateAt k (enableIfForm ft c m))) := by
  rw [generate_text, generate_text]
  apply generate_go_relabel
  apply contribRel_set env args explicit _ decls 0 k _ _ hk
  · rw [Nat.zero_add]
    exact contribution_sameUpToSoft env args explicit _ _ k rfl
      (deduceTemplate_enableIf env ft c m explicit args hcon hq hnd hfp hfr)
  · intro c' hc'; unfold templateAt; simp [show c'.index ≠ k by omega]

/-- sfinae-requires, for the call: the two encodings resolve the call the
same way when ordering the replaced template against the other
candidates is unchanged. Ordering is where subsumption is consulted, and
`sfinae_loses_subsumption` shows it changing. -/
theorem sfinae_requires_resolve (env : Env) (r : Ranking Conv) (decls : List Decl)
    (args : List CallArg) (explicit : List Ty) (k : Nat) (ft : FunctionTemplate) (c : String)
    (m : List Ty) (hk : decls[k]? = some (.functionTemplate (requiresForm ft c m)))
    (hcon : ft.constraint = none)
    (hq : ∀ σ e, env.atomic c (m.map (Ty.subst σ)) ≠ .hard e)
    (hnd : ∀ σ e, nonDependentStep env ft.params args σ ≠ .hard e)
    (hfp : ∀ σ e, formAll env (ft.params.map (Ty.subst σ)) ≠ .hard e)
    (hfr : ∀ σ e, form env (ft.ret.subst σ) ≠ .hard e)
    (hord : ∀ cs, generate .text env decls args explicit = .ok cs → ∀ d ∈ cs, d.index ≠ k →
      ∀ sp, d.specialization = some sp →
        PartialOrdering.moreSpecialized (some args.length) (enableIfForm ft c m) sp.template =
            PartialOrdering.moreSpecialized (some args.length) (requiresForm ft c m) sp.template ∧
          PartialOrdering.moreSpecialized (some args.length) sp.template (enableIfForm ft c m) =
            PartialOrdering.moreSpecialized (some args.length) sp.template (requiresForm ft c m)) :
    resolve .text env r (decls.set k (.functionTemplate (enableIfForm ft c m))) args explicit =
      (resolve .text env r decls args explicit).map (templateAt k (enableIfForm ft c m)) :=
  resolve_relabel env r decls _ args explicit _ (keeps_templateAt k _)
    (sfinae_requires env decls args explicit k ft c m hk hcon hq hnd hfp hfr)
    (ordering_templateAt env decls args explicit k _ _ hk hord)

/-! ## Where the two encodings differ -/

private def T : Ty := .param 0

/-- An unconstrained `g(T)` and one with the condition `empty_like<T>`,
as a requires-clause or as `enable_if`. -/
def subsumptionProgram (sfinae : Bool) : Program :=
  let base : FunctionTemplate := { name := "g", head := [{ kind := .type }], params := [T] }
  [ .class "X", .concept "empty_like" "std::is_empty_v<T>", .functionTemplate base
  , .functionTemplate (if sfinae then enableIfForm base "empty_like" [T]
      else requiresForm base "empty_like" [T]) ]

def subsumptionAtomics : List (String × List Ty × Bool) := [("empty_like", [.named "X"], true)]

/-- Ordering consults subsumption: the requires form is more constrained
than the unconstrained template and wins; the `enable_if` form has no
constraint, and the call is ambiguous. -/
theorem sfinae_loses_subsumption :
    let call := fun p => (invoke .text (Env.ofProgram p subsumptionAtomics) p.ranking
      (p.candidates "g") [{ ty := .named "X" }]).map (·.index)
    call (subsumptionProgram false) = .selected 1 ∧ call (subsumptionProgram true) = .ambiguous [0, 1] :=
  ⟨rfl, rfl⟩

/-- A template whose second parameter's type instantiates a lookup whose
primary fails hard, under the condition `integral_like<T>`. -/
def shieldProgram (sfinae : Bool) : Program :=
  let base : FunctionTemplate :=
    { name := "f", head := [{ kind := .type }], params := [T, .typeOf (.lookup "trait" T)] }
  [ .class "X", .lookupHard "trait", .concept "integral_like" "std::is_integral_v<T>"
  , .functionTemplate (if sfinae then enableIfForm base "integral_like" [T]
      else requiresForm base "integral_like" [T]) ]

def shieldAtomics : List (String × List Ty × Bool) := [("integral_like", [.named "X"], false)]

/-- The step order separates the two: the requires-clause fails before
the function type is substituted, so the call is merely not viable; the
`enable_if` condition, in a trailing return type, is checked only after
the parameter's hard error. -/
theorem sfinae_unshielded :
    let call := fun p => (invoke .text (Env.ofProgram p shieldAtomics) p.ranking
      (p.candidates "f") [{ ty := .named "X" }, { ty := .named "int" }]).map (·.index)
    call (shieldProgram false) = .noMatch ∧ ∃ e, call (shieldProgram true) = .illFormed e :=
  ⟨rfl, ⟨_, rfl⟩⟩

end Overload
