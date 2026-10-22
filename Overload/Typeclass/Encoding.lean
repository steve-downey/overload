-- Overload/Typeclass/Encoding.lean                                   -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Environment
import Overload.Resolution

/-!
# The typeclass encoding: the operation object

Canonical lookup is a variable template, `functor<T>`, whose partial
specializations are the instances; coherence and stability of that lookup
are theorems of the Standard side (`Overload/Lookup.lean`). This module is
the call surface of beman.transpose's encoding over it: the operation
object `fmap`, `template <class F, class T, const auto &TC =
functor<std::remove_cvref_t<T>>> requires requires { TC.fmap(...); } auto
operator()(F &&, T &&) const`, as one function template (`fmapObject`),
and the environment the encoding defines (`encodingEnv`), which answers
the call through the instance as true exactly when the lookup selects an
instance.

* Deducing the operation object for a call follows lookup at the
  container's type with cv and reference removed, and nothing else in the
  program (`fmapObject_deduce`): it succeeds when an instance is selected,
  fails softly when none is, and fails hard only when lookup is ambiguous
  (`fmapObject_outcome`). That discharges the soft-failure and
  normalized-key obligations by construction.
* The specialization names the lookup, not the instance (`fmapSpec`), so
  it does not move when instance positions shift.
* Stability at the call surface (`call_stability`): declaring an instance
  leaves a call's resolution unchanged unless the instance matches the
  key. When it matches, the operation object becomes viable through it, or
  the call is ill-formed by ambiguity. The other candidates must not
  consult the lookup, a hypothesis met by non-template functions outright.
-/

namespace Overload.Typeclass

open PartialOrdering

/-- Does a type have the shape of an instance: an instance and the
pinned instance type have `fmap`, and the primary, `std::false_type`,
has not. -/
def instanceShape : Ty → Bool
  | .spec "instance_of" _ | .named "pinned_instance" => true
  | _ => false

/-- The shape constraint on a type, or on the type of a constant
argument, `decltype(TC)`, which satisfaction evaluates. -/
def fmapShape (t : Ty) : Bool :=
  instanceShape (match t with | .typeOf e => e.typeOfValue | t => t)

/-- The atomic constraints whose meaning is the encoding's: the operation
object's call through its instance, `fmap_call`, true exactly when the
lookup selects an instance, since an instance has the operation and the
primary, `std::false_type`, does not; and the shape constraint of the
by-value route, `fmap_shape`. -/
def memberAtomics (p : Program) : Constraint.Oracle := fun e args =>
  match e, args with
  | "fmap_call", [.ref (.lookup c a), _, _] => .ok ((p.selectInstance c a).toOption.isSome)
  | "fmap_shape", [t] => .ok (fmapShape t)
  | _, _ => .soft s!"unknown atomic constraint {e}"

/-- The environment the encoding defines over a program: the program's
environment (`encodingEnv`), with the encoding's atomic constraints
answered by `memberAtomics`. -/
def encodingEnv (p : Program) (atomics : List (String × List Ty × Bool) := []) : Env :=
  Env.ofProgram p atomics (memberAtomics p)


/-- The operation object `fmap` of beman.transpose, for the typeclass
`tc`: `template <class F, class T, const auto &TC =
tc<std::remove_cvref_t<T>>> requires requires { TC.fmap(...); } auto
operator()(F &&, T &&) const`. A call of the object is resolved as a call
of this one template. -/
def fmapObject (tc : String) : FunctionTemplate :=
  { name := "fmap"
    head :=
      [ { kind := .type }, { kind := .type }
      , { kind := .const (.lref (.const (.named "auto")))
          default := some (.ref (.lookup tc (.removeCvref (.param 1)))) } ]
    params := [.rref (.param 0), .rref (.param 1)]
    constraint := some (.atomic "fmap_call" [.param 2, .param 0, .param 1]) }


theorem fmapObject_call (env : Env) (tc : String) (f x : CallArg) (hf : f.ty.isType = true)
    (hx : x.ty.isType = true) :
    (explicitStep env (fmapObject tc).head [] >>= callStep env (fmapObject tc).params [f, x]) =
      .ok [(1, forwarded x), (0, forwarded f)] := by
  have h0 : Ty.collapse (.rref (.param 0)) = .rref (.param 0) := rfl
  have h1 : Ty.collapse (.rref (.param 1)) = .rref (.param 1) := rfl
  have hl : ∀ t : Ty, (Ty.lref t).isType = true := fun _ => rfl
  cases hlf : f.lvalue <;> cases hlx : x.lvalue <;>
    simp [h0, h1, hl, fmapObject, explicitStep, explicitStep.go, callStep, deduceCall, deduceParam, adjustP,
      adjustA, isForwardingRef, Ty.isRef, Ty.referred, Ty.dependent, Ty.subst, Bindings.lookup,
      deduceTy, bindArg, forwarded, hlf, hlx, hf, hx]



/-- The specialization deduced for a call of the operation object. Its
instance argument is the reference to the lookup, not the instance
selected, so it is the same whichever instance that is. -/
def fmapSpec (tc : String) (f x : CallArg) : Specialization :=
  { template := fmapObject tc
    args := [(2, .ref (.lookup tc x.ty.stripConst)), (1, forwarded x), (0, forwarded f)]
    params := [Ty.collapse (.rref (forwarded f)), Ty.collapse (.rref (forwarded x))]
    ret := .named "void" }

/-- The outcome of deducing the operation object, given the outcome of
instance lookup at its key. -/
def fmapOutcome (tc : String) (f x : CallArg) : Resolution Nat → Subst Specialization
  | .selected _ => .ok (fmapSpec tc f x)
  | .noMatch => .soft "associated constraints not satisfied"
  | .ambiguous _ => .hard s!"ambiguous partial specializations of {tc}<{repr x.ty.stripConst}>"
  | .illFormed r => .hard r

section fmapObject

variable (p : Program) (tc : String) (f x : CallArg)

/-- The bindings after deduction from the call. -/
private abbrev σ₀ : Bindings := [(1, forwarded x), (0, forwarded f)]

/-- The lookup key: the container's type with cv and reference removed. -/
private abbrev key : Ty := x.ty.stripConst

theorem fmapObject_defaults (env : Env) (hx : x.ty.isType = true) (hxF : x.ty.formed = true)
    (hxr : x.ty.isRef = false) (hxd : x.ty.dependent = false) :
    defaultsStep env (fmapObject tc).head (σ₀ f x) =
      (env.instantiate tc (key x)).bind fun _ => .ok ((2, .ref (.lookup tc (key x))) :: σ₀ f x) := by
  have h1 : Ty.subst (σ₀ f x) (.param 1) = forwarded x :=
    subst_param_type _ _ _ (by simp [Bindings.lookup]) (forwarded_isType x hx)
  have hd : Ty.subst (σ₀ f x) (.ref (.lookup tc (.removeCvref (.param 1)))) =
      .ref (.lookup tc (.removeCvref (forwarded x))) := by
    show Ty.ref (Ty.lookup tc (Ty.removeCvref (Ty.subst (σ₀ f x) (.param 1)))) = _
    rw [h1]
  have hform : form env (forwarded x) = .ok (forwarded x) :=
    form_formed env _ (forwarded_formed x hxF hxr)
  simp only [defaultsStep, defaultsStep.go, fmapObject, Bindings.lookup, List.find?]
  simp only [decide_true, decide_false, Option.map_some, Option.map_none, Nat.reduceEqDiff,
    reduceCtorEq]
  rw [hd]
  simp [form, hform, forwarded_dependent, hxd, forwarded_key x hxr, dependent_stripConst]
  cases env.instantiate tc x.ty.stripConst <;> rfl

theorem fmapObject_rest (hf : f.ty.isType = true) (hx : x.ty.isType = true)
    (hfF : f.ty.formed = true) (hxF : x.ty.formed = true)
    (hfr : f.ty.isRef = false) (hxr : x.ty.isRef = false) :
    let env := encodingEnv p
    let σ₁ := (2, Ty.ref (.lookup tc (key x))) :: σ₀ f x
    (parameterListStep env (fmapObject tc).head σ₁ >>= constraintStep env (fmapObject tc).constraint
        >>= nonDependentStep env (fmapObject tc).params [f, x] >>= functionTypeStep env (fmapObject tc)) =
      if (p.selectInstance tc (key x)).toOption.isSome then .ok (fmapSpec tc f x)
      else .soft "associated constraints not satisfied" := by
  intro env σ₁
  have h0 : Ty.subst σ₁ (.param 0) = forwarded f :=
    subst_param_type _ _ _ (by simp [σ₁, Bindings.lookup]) (forwarded_isType f hf)
  have h1 : Ty.subst σ₁ (.param 1) = forwarded x :=
    subst_param_type _ _ _ (by simp [σ₁, Bindings.lookup]) (forwarded_isType x hx)
  have h2 : Ty.subst σ₁ (.param 2) = .ref (.lookup tc (key x)) := by
    simp [Ty.subst, σ₁, Bindings.lookup]
  have hparams : formAll env [Ty.subst σ₁ (.rref (.param 0)), Ty.subst σ₁ (.rref (.param 1))] =
      .ok [Ty.collapse (.rref (forwarded f)), Ty.collapse (.rref (forwarded x))] := by
    show formAll env [Ty.collapse (.rref (Ty.subst σ₁ (.param 0))),
      Ty.collapse (.rref (Ty.subst σ₁ (.param 1)))] = _
    rw [h0, h1]
    simp [formAll, form_formed env _ (collapse_rref_forwarded_formed f hfF hfr),
      form_formed env _ (collapse_rref_forwarded_formed x hxF hxr)]
  have hplist : parameterListStep env (fmapObject tc).head σ₁ = .ok σ₁ := by
    rfl
  have hsat : Constraint.satisfied env.atomic σ₁ (.atomic "fmap_call" [.param 2, .param 0, .param 1]) =
      .ok (p.selectInstance tc (key x)).toOption.isSome := by
    simp only [Constraint.satisfied, List.map, h0, h1, h2]
    simp [env, encodingEnv, Env.ofProgram, memberAtomics]
  rw [hplist]
  simp only [Subst.bind_eq, Subst.bind_ok, constraintStep, fmapObject, hsat]
  cases (p.selectInstance tc (key x)).toOption.isSome
  · simp
  · have hnd : nonDependentStep env [(Ty.param 0).rref, (Ty.param 1).rref] [f, x] σ₁ = .ok σ₁ := rfl
    simp only [↓reduceIte, Subst.pure_eq, Subst.bind_ok, hnd, functionTypeStep, List.map]
    rw [hparams]
    rfl

/-- Deducing the operation object for a call is a function of instance
lookup at the container's type with cv and reference removed, and of
nothing else in the program. -/
theorem fmapObject_deduce (hf : f.ty.isType = true) (hx : x.ty.isType = true)
    (hfF : f.ty.formed = true) (hxF : x.ty.formed = true)
    (hfr : f.ty.isRef = false) (hxr : x.ty.isRef = false) (hxd : x.ty.dependent = false)
    (hsoft : p.any (fun | .lookup c => c = tc | _ => false) = true)
    (hhard : p.any (fun | .lookupHard c => c = tc | _ => false) = false) :
    deduceTemplate (encodingEnv p) (fmapObject tc) [] [f, x] =
      fmapOutcome tc f x (p.selectInstance tc x.ty.stripConst) := by
  have hs := fmapObject_rest p tc f x hf hx hfF hxF hfr hxr
  simp only [Subst.bind_eq] at hs
  have hr : deduceTemplate (encodingEnv p) (fmapObject tc) [] [f, x] =
      ((encodingEnv p).instantiate tc (key x)).bind fun _ =>
      (parameterListStep (encodingEnv p) (fmapObject tc).head ((2, Ty.ref (.lookup tc (key x))) :: σ₀ f x)
        >>= constraintStep (encodingEnv p) (fmapObject tc).constraint
        >>= nonDependentStep (encodingEnv p) (fmapObject tc).params [f, x]
        >>= functionTypeStep (encodingEnv p) (fmapObject tc)) := by
    simp only [deduceTemplate]
    rw [fmapObject_call _ tc f x hf hx]
    simp only [Subst.bind_eq, Subst.bind_ok]
    rw [fmapObject_defaults tc f x _ hx hxF hxr hxd]
    cases (encodingEnv p).instantiate tc (key x) <;> rfl
  have hinst : (encodingEnv p).instantiate tc (key x) =
      match p.selectInstance tc (key x) with
      | .selected i => .ok (.spec' "instance_of" [key x, .value (.int i)])
      | .ambiguous _ => .hard s!"ambiguous partial specializations of {tc}<{repr (key x)}>"
      | .illFormed r => .hard r
      | .noMatch => .ok (.named "std::false_type") :=
    Env.ofProgram_instantiate p [] (memberAtomics p) tc (key x) hsoft hhard
  rw [hr, hinst]
  cases hl : p.selectInstance tc (key x) with
  | selected i =>
    simp only [Subst.bind_eq, Subst.bind_ok]
    rw [hs, hl]
    rfl
  | noMatch =>
    simp only [Subst.bind_eq, Subst.bind_ok]
    rw [hs, hl]
    rfl
  | ambiguous l => rfl
  | illFormed r => rfl

/-- The operation object at the call surface. For a program whose lookup
has the soft default, `std::false_type`, deducing the operation object
for a call follows instance lookup at the container's type with cv and
reference removed. It succeeds when an instance is selected. A missing
instance is a deduction failure, so the call is merely not viable: the
soft-failure obligation, discharged by construction. Only an ambiguous
lookup is a hard error. The arguments are formed, non-reference,
non-dependent types, as the arguments of a call are. -/
theorem fmapObject_outcome (hf : f.ty.isType = true) (hx : x.ty.isType = true)
    (hfF : f.ty.formed = true) (hxF : x.ty.formed = true)
    (hfr : f.ty.isRef = false) (hxr : x.ty.isRef = false) (hxd : x.ty.dependent = false)
    (hsoft : p.any (fun | .lookup c => c = tc | _ => false) = true)
    (hhard : p.any (fun | .lookupHard c => c = tc | _ => false) = false) :
    let r := deduceTemplate (encodingEnv p) (fmapObject tc) [] [f, x]
    (∀ i, p.selectInstance tc x.ty.stripConst = .selected i → ∃ s, r = .ok s) ∧
    (p.selectInstance tc x.ty.stripConst = .noMatch → ∃ e, r = .soft e) ∧
    (∀ l, p.selectInstance tc x.ty.stripConst = .ambiguous l → ∃ e, r = .hard e) := by
  intro r
  have hd : r = _ := fmapObject_deduce p tc f x hf hx hfF hxF hfr hxr hxd hsoft hhard
  refine ⟨fun i hi => ?_, fun hn => ?_, fun l hl => ?_⟩
  · rw [hd, hi]; exact ⟨_, rfl⟩
  · rw [hd, hn]; exact ⟨_, rfl⟩
  · rw [hd, hl]; exact ⟨_, rfl⟩

end fmapObject

/-! ## Stability at the call surface -/

theorem fmapOutcome_map (tc : String) (f x : CallArg) (g : Nat → Nat) (r : Resolution Nat) :
    fmapOutcome tc f x (r.map g) = fmapOutcome tc f x r := by
  cases r <;> rfl

/-- Declaring an instance does not change which lookups a program
declares. -/
theorem any_insert_instance (p₁ p₂ : Program) (tc : String) (h : Head) (pat : Ty)
    (g : Decl → Bool) (hg : g (.instance tc h pat) = false) :
    (p₁ ++ .instance tc h pat :: p₂).any g = (p₁ ++ p₂).any g := by
  simp [List.any_append, hg]

/-- Stability of a call of the operation object. Declaring an instance
anywhere in a program leaves the resolution of the call unchanged unless
the new instance matches the container's type with cv and reference
removed. When it matches, the operation object becomes viable through the
new instance, or lookup is ambiguous and, under the text, the call is
ill-formed. The other candidates are any non-template functions and any
templates whose deduction does not consult the lookup; that is the
hypothesis `hothers`, which a template that also looks up `tc` would have
to meet through stability of its own lookups. -/
theorem call_stability (p₁ p₂ : Program) (tc : String) (h : Head) (pat : Ty) (r : Ranking Conv)
    (decls : List Decl) (f x : CallArg)
    (hf : f.ty.isType = true) (hx : x.ty.isType = true)
    (hfF : f.ty.formed = true) (hxF : x.ty.formed = true)
    (hfr : f.ty.isRef = false) (hxr : x.ty.isRef = false) (hxd : x.ty.dependent = false)
    (hsoft : (p₁ ++ p₂).any (fun | .lookup c => c = tc | _ => false) = true)
    (hhard : (p₁ ++ p₂).any (fun | .lookupHard c => c = tc | _ => false) = false)
    (hm : .functionTemplate (fmapObject tc) ∈ decls) :
    let p := p₁ ++ p₂
    let p' := p₁ ++ .instance tc h pat :: p₂
    (∀ ft, .functionTemplate ft ∈ decls → ft ≠ fmapObject tc →
      deduceTemplate (encodingEnv p') ft [] [f, x] = deduceTemplate (encodingEnv p) ft [] [f, x]) →
    resolve .text (encodingEnv p') r decls [f, x] = resolve .text (encodingEnv p) r decls [f, x] ∨
    (PatternMatches h pat x.ty.stripConst ∧
      (p'.selectInstance tc x.ty.stripConst = .selected (p₁.instancesOf tc).length ∨
        ∃ e, resolve .text (encodingEnv p') r decls [f, x] = .illFormed e)) := by
  intro p p' hothers
  have hsoft' : p'.any (fun | .lookup c => c = tc | _ => false) = true := by
    rw [any_insert_instance _ _ _ _ _ _ rfl]; exact hsoft
  have hhard' : p'.any (fun | .lookupHard c => c = tc | _ => false) = false := by
    rw [any_insert_instance _ _ _ _ _ _ rfl]; exact hhard
  have hd := fmapObject_deduce p tc f x hf hx hfF hxF hfr hxr hxd hsoft hhard
  have hd' := fmapObject_deduce p' tc f x hf hx hfF hxF hfr hxr hxd hsoft' hhard'
  have hcongr : deduceTemplate (encodingEnv p') (fmapObject tc) [] [f, x] =
      deduceTemplate (encodingEnv p) (fmapObject tc) [] [f, x] →
      resolve .text (encodingEnv p') r decls [f, x] = resolve .text (encodingEnv p) r decls [f, x] :=
    fun he => resolve_congr _ _ _ r decls _ fun ft hft => by
      by_cases hft' : ft = fmapObject tc
      · subst hft'; exact he
      · exact hothers ft hft hft'
  rcases stability p₁ p₂ tc h pat x.ty.stripConst with e | ⟨hmatch, e | ⟨l, e⟩⟩
  · refine .inl (hcongr ?_)
    rw [hd', hd, e, fmapOutcome_map]
  · exact .inr ⟨hmatch, .inl e⟩
  · refine .inr ⟨hmatch, .inr ?_⟩
    rw [e] at hd'
    exact resolve_text_hard _ r decls _ _ _ hm hd'


end Overload.Typeclass
