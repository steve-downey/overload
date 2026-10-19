-- Overload/Typeclass/Routes.lean                                     -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Typeclass.Encoding

/-!
# The other ways an instance reaches a call

The canonical route is the operation object's defaulted instance
parameter (`Overload/Typeclass/Encoding.lean`). The library and its
examples have two more, and the plan proposed three others as overloads,
which `decisions.md#explicit-instance-routes` settles.

* Pinning (`pinTemplate`): a user function template whose trailing
  reference parameter defaults to the lookup, with no constraint. Pinned,
  deduction never instantiates the lookup, so the outcome is the same in
  every program (`pinned_deduce`). Unpinned, a missing instance binds the
  primary and the call is viable: the error is in the body
  (`unpinned_deduce`).
* The by-value route (`byValueObject`): `traverse`'s policy, reduced to
  `fmap`, with the policy type defaulted to the type of the lookup's value
  and a shape constraint. Omitted, it follows lookup and fails softly only
  because the primary's type has no instance's shape
  (`byValue_omitted_outcome`). Passed, it never instantiates the lookup
  (`byValue_passed`).
* The plan's three routes (`valueRoute`, `typeRoute`, `argumentRoute`),
  as an alternative design beside the canonical object, so the guidance
  can compare them; the emitted cases show where they separate and where
  the type route is exposed (`docs/findings.md`).
-/

namespace Overload.Typeclass

/-! ## Pinning -/

/-- The pinning pattern of beman.transpose's examples: a user function
template whose trailing reference parameter defaults to the lookup,
`template <class C, const auto &TC = tc<C>> void name(const C &)`. The
body calls through `TC`, and there is no constraint. A caller pins an
instance by specifying `TC` explicitly. -/
def pinTemplate (tc name : String) : FunctionTemplate :=
  { name
    head :=
      [ { kind := .type }
      , { kind := .const (.lref (.const (.named "auto")))
          default := some (.ref (.lookup tc (.param 0))) } ]
    params := [.lref (.const (.param 0))] }

/-- The specialization of the pinning template at `C = c` with instance
argument `inst`. -/
def pinSpec (tc name : String) (c inst : Ty) : Specialization :=
  { template := pinTemplate tc name, args := [(1, inst), (0, c)]
    params := [.lref (.const c)], ret := .named "void" }

/-- Pinned: with `C` and the instance specified, deduction never
substitutes the default, so it never instantiates the lookup. The
outcome is the same in every environment, whatever the program's
instances are, including none and an ambiguous pair. -/
theorem pinned_deduce (env : Env) (tc name o : String) (c : Ty) (x : CallArg)
    (hc : c.isType = true) (hcd : c.dependent = false) (hcF : c.formed = true)
    (hcr : c.isRef = false) :
    deduceTemplate env (pinTemplate tc name) [c, .ref (.named o)] [x] =
      .ok (pinSpec tc name c (.ref (.named o))) := by
  have hsub : Ty.subst [(1, .ref (.named o)), (0, c)] (.lref (.const (.param 0))) =
      .lref (.const c) := by
    have h0 : Ty.subst [(1, .ref (.named o)), (0, c)] (.param 0) = c :=
      subst_param_type _ _ _ (by simp [Bindings.lookup]) hc
    show Ty.collapse (.lref (.const (Ty.subst _ (.param 0)))) = _
    rw [h0]
    rfl
  have hform : form env (.lref (.const c)) = .ok (.lref (.const c)) :=
    form_formed env _ (by simp [Ty.formed, hcF, Ty.isRef] at *; exact hcr)
  have hcall : callStep env (pinTemplate tc name).params [x] [(1, .ref (.named o)), (0, c)] =
      .ok [(1, .ref (.named o)), (0, c)] := by
    simp only [callStep, pinTemplate, List.map, hsub, deduceCall, deduceParam, Ty.dependent, hcd]
    rfl
  have hexp : explicitStep (pinTemplate tc name).head [c, .ref (.named o)] =
      .ok [(1, .ref (.named o)), (0, c)] := by
    simp [explicitStep, explicitStep.go, pinTemplate, kindMatches, hc]
    rfl
  have hdef : defaultsStep env (pinTemplate tc name).head [(1, .ref (.named o)), (0, c)] =
      .ok [(1, .ref (.named o)), (0, c)] := by
    simp [defaultsStep, defaultsStep.go, Bindings.lookup, pinTemplate]
  have hft : functionTypeStep env (pinTemplate tc name) [(1, .ref (.named o)), (0, c)] =
      .ok (pinSpec tc name c (.ref (.named o))) := by
    simp only [functionTypeStep, pinTemplate, List.map, hsub, formAll, hform, Subst.bind_eq,
      Subst.bind_ok, Subst.pure_eq]
    rfl
  simp only [deduceTemplate, Subst.bind_eq]
  rw [hexp, Subst.bind_ok, hcall, Subst.bind_ok, hdef, Subst.bind_ok]
  exact hft

/-- The outcome of deducing the unpinned template, given the outcome of
instance lookup at its key. -/
def pinOutcome (tc name : String) (c : Ty) : Resolution Nat → Subst Specialization
  | .selected _ | .noMatch => .ok (pinSpec tc name c (.ref (.lookup tc c)))
  | .ambiguous _ => .hard s!"ambiguous partial specializations of {tc}<{repr c}>"
  | .illFormed r => .hard r

theorem pin_call (env : Env) (tc name : String) (x : CallArg) (hx : x.ty.isType = true)
    (hk : x.ty.stripConst.isType = true) :
    callStep env (pinTemplate tc name).params [x] [] = .ok [(0, x.ty.stripConst)] := by
  cases h : x.ty <;> simp_all [callStep, pinTemplate, deduceCall, deduceParam, adjustP, adjustA,
    isForwardingRef, Ty.isRef, Ty.referred, Ty.dependent, Ty.subst, Bindings.lookup, deduceTy,
    bindArg, Ty.stripConst, Ty.collapse] <;> rfl

/-- Unpinned, the pinning template takes the canonical instance, but it
has no constraint: a missing instance binds the primary and the call is
viable. The soft-failure obligation is not discharged by the pattern; a
missing instance becomes an error in the body. Only an ambiguous lookup
fails deduction, and it fails hard. -/
theorem unpinned_deduce (p : Program) (tc name : String) (x : CallArg)
    (hx : x.ty.isType = true) (hk : x.ty.stripConst.isType = true)
    (hkF : x.ty.stripConst.formed = true) (hkr : x.ty.stripConst.isRef = false)
    (hkd : x.ty.stripConst.dependent = false)
    (hsoft : p.any (fun | .lookup c => c = tc | _ => false) = true)
    (hhard : p.any (fun | .lookupHard c => c = tc | _ => false) = false) :
    deduceTemplate (encodingEnv p) (pinTemplate tc name) [] [x] =
      pinOutcome tc name x.ty.stripConst (p.selectInstance tc x.ty.stripConst) := by
  generalize hc : x.ty.stripConst = c at *
  have h0 : Ty.subst [(0, c)] (.param 0) = c := subst_param_type _ _ _ (by simp [Bindings.lookup]) hk
  have hσ : ∀ σ : Bindings, σ = [(1, .ref (.lookup tc c)), (0, c)] →
      Ty.subst σ (.lref (.const (.param 0))) = .lref (.const c) := by
    rintro σ rfl
    have h0' : Ty.subst [(1, .ref (.lookup tc c)), (0, c)] (.param 0) = c :=
      subst_param_type _ _ _ (by simp [Bindings.lookup]) hk
    show Ty.collapse (.lref (.const (Ty.subst _ (.param 0)))) = _
    rw [h0']
    rfl
  have hform : ∀ env, form env (.lref (.const c)) = .ok (.lref (.const c)) := fun env =>
    form_formed env _ (by simp [Ty.formed, hkF, Ty.isRef] at *; exact hkr)
  have hdef : defaultsStep (encodingEnv p) (pinTemplate tc name).head [(0, c)] =
      ((encodingEnv p).instantiate tc c).bind fun _ => .ok [(1, .ref (.lookup tc c)), (0, c)] := by
    have hd : Ty.subst [(0, c)] (.ref (.lookup tc (.param 0))) = .ref (.lookup tc c) := by
      show Ty.ref (Ty.lookup tc (Ty.subst _ (.param 0))) = _
      rw [h0]
    simp only [defaultsStep, defaultsStep.go, pinTemplate, Bindings.lookup, List.find?]
    simp only [decide_true, decide_false, Option.map_some, Option.map_none,
      reduceCtorEq]
    rw [hd]
    simp [form, form_formed _ _ hkF, hkd]
    cases (encodingEnv p).instantiate tc c <;> rfl
  have hft : functionTypeStep (encodingEnv p) (pinTemplate tc name) [(1, .ref (.lookup tc c)), (0, c)] =
      .ok (pinSpec tc name c (.ref (.lookup tc c))) := by
    simp only [functionTypeStep, pinTemplate, List.map, hσ _ rfl, formAll, hform, Subst.bind_eq,
      Subst.bind_ok, Subst.pure_eq]
    rfl
  have hinst : (encodingEnv p).instantiate tc c =
      match p.selectInstance tc c with
      | .selected i => .ok (.spec' "instance_of" [c, .value (.int i)])
      | .ambiguous _ => .hard s!"ambiguous partial specializations of {tc}<{repr c}>"
      | .illFormed r => .hard r
      | .noMatch => .ok (.named "std::false_type") :=
    Env.ofProgram_instantiate p [] (memberAtomics p) tc c hsoft hhard
  have hcall := pin_call (encodingEnv p) tc name x hx (hc ▸ hk)
  rw [hc] at hcall
  simp only [deduceTemplate, Subst.bind_eq]
  rw [show explicitStep (pinTemplate tc name).head [] = .ok [] from rfl, Subst.bind_ok, hcall,
    Subst.bind_ok, hdef, hinst]
  cases p.selectInstance tc c with
  | selected i => exact hft
  | noMatch => exact hft
  | ambiguous l => rfl
  | illFormed r => rfl

/-! ## The by-value route -/

/-- The by-value route of beman.transpose, `traverse`'s `POLICY`, reduced
to `fmap`: `template <class F, class T, class P =
std::remove_cvref_t<decltype(tc<std::remove_cvref_t<T>>)>> requires
fmap_shape<P> void fmap_with(F &&, T &&, P = P{})`. A caller supplies an
instance by passing it as the third argument, and the instance enters
the specialization by its type. The constraint checks the shape of the
type, which is what makes a missing instance a soft failure. -/
def byValueObject (tc : String) : FunctionTemplate :=
  { name := "fmap_with"
    head :=
      [ { kind := .type }, { kind := .type }
      , { kind := .type, default := some (.typeOf (.lookup tc (.removeCvref (.param 1)))) } ]
    params := [.rref (.param 0), .rref (.param 1), .param 2]
    defaultArgs := 1
    constraint := some (.atomic "fmap_shape" [.param 2]) }

theorem byValue_call_omitted (env : Env) (tc : String) (f x : CallArg) (hf : f.ty.isType = true)
    (hx : x.ty.isType = true) :
    (explicitStep (byValueObject tc).head [] >>= callStep env (byValueObject tc).params [f, x]) =
      .ok [(1, forwarded x), (0, forwarded f)] := by
  have h0 : Ty.collapse (.rref (.param 0)) = .rref (.param 0) := rfl
  have h1 : Ty.collapse (.rref (.param 1)) = .rref (.param 1) := rfl
  have hl : ∀ t : Ty, (Ty.lref t).isType = true := fun _ => rfl
  cases hlf : f.lvalue <;> cases hlx : x.lvalue <;>
    simp [h0, h1, hl, byValueObject, explicitStep, explicitStep.go, callStep, deduceCall, deduceParam,
      adjustP, adjustA, isForwardingRef, Ty.isRef, Ty.referred, Ty.dependent, Ty.subst, Bindings.lookup,
      deduceTy, bindArg, forwarded, hlf, hlx, hf, hx]

/-- The specialization of the by-value route with policy type `v`. Its
policy argument is the instance's type, so it names the instance. -/
def byValueSpec (tc : String) (f x : CallArg) (v : Ty) : Specialization :=
  { template := byValueObject tc, args := [(2, v), (1, forwarded x), (0, forwarded f)]
    params := [Ty.collapse (.rref (forwarded f)), Ty.collapse (.rref (forwarded x)), v]
    ret := .named "void" }

section byValue

variable (p : Program) (tc : String) (f x : CallArg)

theorem byValue_defaults (env : Env) (hx : x.ty.isType = true) (hxF : x.ty.formed = true)
    (hxr : x.ty.isRef = false) (hxd : x.ty.dependent = false) :
    defaultsStep env (byValueObject tc).head [(1, forwarded x), (0, forwarded f)] =
      (env.instantiate tc x.ty.stripConst).bind fun v =>
        .ok ((2, if v.dependent then .typeOf v else v.typeOfValue) :: [(1, forwarded x), (0, forwarded f)]) := by
  have h1 : Ty.subst [(1, forwarded x), (0, forwarded f)] (.param 1) = forwarded x :=
    subst_param_type _ _ _ (by simp [Bindings.lookup]) (forwarded_isType x hx)
  have hd : Ty.subst [(1, forwarded x), (0, forwarded f)] (.typeOf (.lookup tc (.removeCvref (.param 1)))) =
      .typeOf (.lookup tc (.removeCvref (forwarded x))) := by
    show Ty.typeOf (Ty.lookup tc (Ty.removeCvref (Ty.subst _ (.param 1)))) = _
    rw [h1]
  have hform : form env (forwarded x) = .ok (forwarded x) :=
    form_formed env _ (forwarded_formed x hxF hxr)
  simp only [defaultsStep, defaultsStep.go, byValueObject, Bindings.lookup, List.find?]
  simp only [decide_true, decide_false, Option.map_some, reduceCtorEq]
  rw [hd]
  simp [form, hform, forwarded_dependent, hxd, forwarded_key x hxr, dependent_stripConst]
  cases env.instantiate tc x.ty.stripConst <;> rfl

/-- After the defaults, with the policy type `v`, the steps that remain
succeed exactly when `v` has the shape of an instance. -/
theorem byValue_rest (hf : f.ty.isType = true) (hx : x.ty.isType = true)
    (hfF : f.ty.formed = true) (hxF : x.ty.formed = true)
    (hfr : f.ty.isRef = false) (hxr : x.ty.isRef = false)
    (v : Ty) (hv : v.isType = true) (hvF : v.formed = true) (as : List CallArg) :
    let env := encodingEnv p
    let σ₁ := (2, v) :: [(1, forwarded x), (0, forwarded f)]
    (parameterListStep env (byValueObject tc).head σ₁ >>= constraintStep env (byValueObject tc).constraint
        >>= nonDependentStep env (byValueObject tc).params as >>= functionTypeStep env (byValueObject tc)) =
      if fmapShape v then .ok (byValueSpec tc f x v)
      else .soft "associated constraints not satisfied" := by
  intro env σ₁
  have h0 : Ty.subst σ₁ (.param 0) = forwarded f :=
    subst_param_type _ _ _ (by simp [σ₁, Bindings.lookup]) (forwarded_isType f hf)
  have h1 : Ty.subst σ₁ (.param 1) = forwarded x :=
    subst_param_type _ _ _ (by simp [σ₁, Bindings.lookup]) (forwarded_isType x hx)
  have h2 : Ty.subst σ₁ (.param 2) = v :=
    subst_param_type _ _ _ (by simp [σ₁, Bindings.lookup]) hv
  have hparams : formAll env [Ty.subst σ₁ (.rref (.param 0)), Ty.subst σ₁ (.rref (.param 1)),
      Ty.subst σ₁ (.param 2)] =
      .ok [Ty.collapse (.rref (forwarded f)), Ty.collapse (.rref (forwarded x)), v] := by
    show formAll env [Ty.collapse (.rref (Ty.subst σ₁ (.param 0))),
      Ty.collapse (.rref (Ty.subst σ₁ (.param 1))), Ty.subst σ₁ (.param 2)] = _
    rw [h0, h1, h2]
    simp [formAll, form_formed env _ (collapse_rref_forwarded_formed f hfF hfr),
      form_formed env _ (collapse_rref_forwarded_formed x hxF hxr), form_formed env _ hvF]
  have hplist : parameterListStep env (byValueObject tc).head σ₁ = .ok σ₁ := rfl
  have hsat : Constraint.satisfied env.atomic σ₁ (.atomic "fmap_shape" [.param 2]) =
      .ok (fmapShape v) := by
    simp only [Constraint.satisfied, List.map, h2]
    simp [env, encodingEnv, Env.ofProgram, memberAtomics]
  rw [hplist]
  simp only [Subst.bind_eq, Subst.bind_ok, constraintStep, byValueObject, hsat]
  cases fmapShape v
  · simp
  · have hnd : nonDependentStep env [(Ty.param 0).rref, (Ty.param 1).rref, .param 2] as σ₁ =
        .ok σ₁ := by
      rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨c, as⟩⟩⟩ <;> rfl
    simp only [↓reduceIte, Subst.pure_eq, Subst.bind_ok, hnd, functionTypeStep, List.map]
    rw [hparams]
    rfl

/-- The by-value route with the policy omitted. Deduction follows lookup
at the container's type with cv and reference removed: it succeeds when
an instance is selected, and fails hard when lookup is ambiguous. A
missing instance fails softly, but only because the primary's type,
`std::false_type`, does not have the shape the constraint checks: the
soft failure rests on the shapeless-default obligation. -/
theorem byValue_omitted_outcome (hf : f.ty.isType = true) (hx : x.ty.isType = true)
    (hfF : f.ty.formed = true) (hxF : x.ty.formed = true)
    (hfr : f.ty.isRef = false) (hxr : x.ty.isRef = false) (hxd : x.ty.dependent = false)
    (hsoft : p.any (fun | .lookup c => c = tc | _ => false) = true)
    (hhard : p.any (fun | .lookupHard c => c = tc | _ => false) = false) :
    let r := deduceTemplate (encodingEnv p) (byValueObject tc) [] [f, x]
    (∀ i, p.selectInstance tc x.ty.stripConst = .selected i → ∃ s, r = .ok s) ∧
    (p.selectInstance tc x.ty.stripConst = .noMatch → ∃ e, r = .soft e) ∧
    (∀ l, p.selectInstance tc x.ty.stripConst = .ambiguous l → ∃ e, r = .hard e) := by
  intro r
  have hr : r = ((encodingEnv p).instantiate tc x.ty.stripConst).bind fun v =>
      (parameterListStep (encodingEnv p) (byValueObject tc).head
          ((2, if v.dependent then .typeOf v else v.typeOfValue) :: [(1, forwarded x), (0, forwarded f)])
        >>= constraintStep (encodingEnv p) (byValueObject tc).constraint
        >>= nonDependentStep (encodingEnv p) (byValueObject tc).params [f, x]
        >>= functionTypeStep (encodingEnv p) (byValueObject tc)) := by
    simp only [r, deduceTemplate]
    rw [byValue_call_omitted _ tc f x hf hx]
    simp only [Subst.bind_eq, Subst.bind_ok]
    rw [byValue_defaults tc f x _ hx hxF hxr hxd]
    cases (encodingEnv p).instantiate tc x.ty.stripConst <;> rfl
  have hinst : (encodingEnv p).instantiate tc x.ty.stripConst =
      match p.selectInstance tc x.ty.stripConst with
      | .selected i => .ok (.spec' "instance_of" [x.ty.stripConst, .value (.int i)])
      | .ambiguous _ => .hard s!"ambiguous partial specializations of {tc}<{repr x.ty.stripConst}>"
      | .illFormed r => .hard r
      | .noMatch => .ok (.named "std::false_type") :=
    Env.ofProgram_instantiate p [] (memberAtomics p) tc x.ty.stripConst hsoft hhard
  have hkF := formed_stripConst _ hxF
  have hkd : x.ty.stripConst.dependent = false := by rw [dependent_stripConst]; exact hxd
  refine ⟨fun i hi => ?_, fun hn => ?_, fun l hl => ?_⟩
  · let v : Ty := .spec' "instance_of" [x.ty.stripConst, .value (.int i)]
    have hvd : v.dependent = false := by
      simp [v, Ty.spec', Ty.args, Ty.dependent, hkd, Val.dependent]
    have hvF : v.formed = true := by
      simp [v, Ty.spec', Ty.args, Ty.formed, hkF]
    have hs := byValue_rest p tc f x hf hx hfF hxF hfr hxr v rfl hvF [f, x]
    refine ⟨byValueSpec tc f x v, ?_⟩
    rw [hr, hinst, hi]
    simp only [Subst.bind_eq, Subst.bind_ok]
    simp only [Subst.bind_eq] at hs
    rw [show (if v.dependent = true then Ty.typeOf v else v.typeOfValue) = v by
      simp only [hvd, Bool.false_eq_true, ↓reduceIte]; rfl]
    rw [hs]
    simp [fmapShape, instanceShape, v, Ty.spec']
  · have hs := byValue_rest p tc f x hf hx hfF hxF hfr hxr (.named "std::false_type") rfl rfl [f, x]
    refine ⟨"associated constraints not satisfied", ?_⟩
    rw [hr, hinst, hn]
    simp only [Subst.bind_eq, Subst.bind_ok]
    simp only [Subst.bind_eq] at hs
    exact hs
  · refine ⟨s!"ambiguous partial specializations of {tc}<{repr x.ty.stripConst}>", ?_⟩
    rw [hr, hinst, hl]
    rfl

theorem byValue_call_passed (env : Env) (hf : f.ty.isType = true) (hx : x.ty.isType = true) (pol : CallArg)
    (hk : pol.ty.stripConst.isType = true) :
    (explicitStep (byValueObject tc).head [] >>= callStep env (byValueObject tc).params [f, x, pol]) =
      .ok [(2, pol.ty.stripConst), (1, forwarded x), (0, forwarded f)] := by
  have h0 : Ty.collapse (.rref (.param 0)) = .rref (.param 0) := rfl
  have h1 : Ty.collapse (.rref (.param 1)) = .rref (.param 1) := rfl
  have hl : ∀ t : Ty, (Ty.lref t).isType = true := fun _ => rfl
  have h2 : (Ty.param 2).stripConst = .param 2 := rfl
  cases hlf : f.lvalue <;> cases hlx : x.lvalue <;>
    simp [h0, h1, h2, hl, byValueObject, explicitStep, explicitStep.go, callStep, deduceCall,
      deduceParam, adjustP, adjustA, isForwardingRef, Ty.isRef, Ty.referred, Ty.dependent, Ty.subst,
      Bindings.lookup, deduceTy, bindArg, forwarded, hlf, hlx, hf, hx, hk]

/-- The by-value route with the policy passed. The policy type is deduced
from the argument and the default is never substituted, so the outcome
does not mention the program's instances: it is the same with none, with
an ambiguous pair, or with any other. The call is viable exactly when the
policy has the shape of an instance. -/
theorem byValue_passed (hf : f.ty.isType = true) (hx : x.ty.isType = true)
    (hfF : f.ty.formed = true) (hxF : x.ty.formed = true)
    (hfr : f.ty.isRef = false) (hxr : x.ty.isRef = false) (pol : CallArg)
    (hk : pol.ty.stripConst.isType = true) (hkF : pol.ty.stripConst.formed = true) :
    deduceTemplate (encodingEnv p) (byValueObject tc) [] [f, x, pol] =
      if fmapShape pol.ty.stripConst then .ok (byValueSpec tc f x pol.ty.stripConst)
      else .soft "associated constraints not satisfied" := by
  have hdef : defaultsStep (encodingEnv p) (byValueObject tc).head
      [(2, pol.ty.stripConst), (1, forwarded x), (0, forwarded f)] =
      .ok [(2, pol.ty.stripConst), (1, forwarded x), (0, forwarded f)] := by
    simp [defaultsStep, defaultsStep.go, Bindings.lookup, byValueObject]
  have hs := byValue_rest p tc f x hf hx hfF hxF hfr hxr pol.ty.stripConst hk hkF [f, x, pol]
  simp only [Subst.bind_eq] at hs
  simp only [deduceTemplate]
  rw [byValue_call_passed tc f x _ hf hx pol hk]
  simp only [Subst.bind_eq, Subst.bind_ok]
  rw [hdef, Subst.bind_ok]
  exact hs

end byValue

/-! ## The plan's routes, as an alternative design

The plan proposed three explicit-instance routes as overloads beside the
canonical one, which beman.transpose does not have
(`decisions.md#explicit-instance-routes`). They are given here so the
guidance can compare them with the library: the instance as a constant
template argument by value, as a type template argument, and as a
trailing function argument with no default. Each is constrained by the
shape of the instance's type, and none consults the lookup. The explicit
instance comes first in the two template-parameter routes, since
explicit template arguments bind the leading parameters. -/

/-- `template <auto TC, class F, class T> requires
fmap_shape<std::remove_cvref_t<decltype(TC)>> void fmap(F &&, T &&)`. -/
def valueRoute : FunctionTemplate :=
  { name := "fmap"
    head := [ { kind := .const (.named "auto") }, { kind := .type }, { kind := .type } ]
    params := [.rref (.param 1), .rref (.param 2)]
    constraint := some (.atomic "fmap_shape" [.typeOf (.value (.param 0))]) }

/-- `template <class TC, class F, class T> requires fmap_shape<TC> void
fmap(F &&, T &&)`. -/
def typeRoute : FunctionTemplate :=
  { name := "fmap"
    head := [ { kind := .type }, { kind := .type }, { kind := .type } ]
    params := [.rref (.param 1), .rref (.param 2)]
    constraint := some (.atomic "fmap_shape" [.param 0]) }

/-- `template <class F, class T, class P> requires fmap_shape<P> void
fmap(F &&, T &&, P)`: the by-value route with the policy required. With
a default it would be viable for every call the canonical overload is,
and the two would not be ordered (`routes_argument_default_ambiguous`). -/
def argumentRoute : FunctionTemplate :=
  { name := "fmap"
    head := [ { kind := .type }, { kind := .type }, { kind := .type } ]
    params := [.rref (.param 0), .rref (.param 1), .param 2]
    constraint := some (.atomic "fmap_shape" [.param 2]) }


end Overload.Typeclass
