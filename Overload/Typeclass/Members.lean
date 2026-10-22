-- Overload/Typeclass/Members.lean                                    -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Conjunction
import Overload.Access
import Overload.Typeclass.Encoding

/-!
# The instance's members, and what the operation object makes of them

The model does not resolve the call through an instance, `TC.fmap(...)`.
It is the operation object's constraint, an atomic constraint answered by
the environment, and `encodingEnv` answers it as accurately as possible:
true exactly when the lookup selects an instance. That is a hypothesis
about the library, and an audit of beman.transpose found it false for
members of every typeclass (`docs/findings.md#about-the-library`). A
member with no constraint and a deduced return type makes the answer a
hard error; a constraint weaker than its body makes it true where the
call then fails.

This module states the hypothesis as a parameter, and proves four things
about it.

* The operation object adds nothing and loses nothing (`fmapObject_member`):
  for any answer the member call gives, deduction of the operation object
  is that answer, once the lookup has been instantiated. A member that is
  accurate gives a call that is viable or not viable; a member whose
  answer is a hard error gives an ill-formed call (`inaccurate_member_ill_formed`).
  `encodingEnv` is the accurate member (`ofProgram_member`).
* An operation object may have several `operator()`s that differ by arity,
  as `fold_map` and `combine_all` do, without another one reaching the
  lookup, provided each places the lookup default after a parameter the
  shorter call cannot deduce (`arity_disjoint_soft`, `call_stability_arity`).
  The order matters: with the default first, the shorter call substitutes
  the lookup in the longer overload, and an ambiguous lookup is a hard
  error there (`arity_order_matters`).
* A registry that tests for an instance by completeness, as `Monoid` does,
  has exactly the verdicts of a lookup, under a third rule where the answer
  of the test changes: `registry_verdicts` in `Overload/Units.lean`, with
  `Monoid` as the registry.
* An algorithm over an instance whose constraint is the conjunction of its
  member calls answers as those calls do, in the order written
  (`algorithm_transfer`), and is accurate when they are
  (`algorithm_accurate`). A call written after one that is not satisfied
  is never checked (`call_order_matters`).
-/

namespace Overload.Typeclass

open PartialOrdering

/-! ## The member call, as a parameter -/

/-- What deducing the operation object makes of the answer of the member
call: a true answer is the specialization, a false or invalid one is a
constraint that is not satisfied, and a hard error stays one. -/
def memberOutcome (s : Specialization) : Subst Bool → Subst Specialization
  | .ok true => .ok s
  | .ok false => .soft "associated constraints not satisfied"
  | .soft _ => .soft "associated constraints not satisfied"
  | .hard r => .hard r

/-- How satisfaction reads an atomic constraint's answer: an invalid
expression is not satisfied, and anything else stands. -/
def memberArgs (tc : String) (f x : CallArg) : List Ty :=
  [.ref (.lookup tc x.ty.stripConst), forwarded f, forwarded x]

section member

variable (tc : String) (f x : CallArg)

/-- After the defaults, the steps that remain are the member call's answer
and nothing else. -/
theorem fmapObject_rest_member (env : Env) (v : Subst Bool)
    (hv : env.atomic "fmap_call" (memberArgs tc f x) = v)
    (hf : f.ty.isType = true) (hx : x.ty.isType = true)
    (hfF : f.ty.formed = true) (hxF : x.ty.formed = true)
    (hfr : f.ty.isRef = false) (hxr : x.ty.isRef = false) :
    let σ₁ : Bindings := [(2, Ty.ref (.lookup tc x.ty.stripConst)), (1, forwarded x), (0, forwarded f)]
    (parameterListStep env (fmapObject tc).head σ₁ >>= constraintStep env (fmapObject tc).constraint
        >>= nonDependentStep env (fmapObject tc).params [f, x] >>= functionTypeStep env (fmapObject tc)) =
      memberOutcome (fmapSpec tc f x) v := by
  intro σ₁
  have h0 : Ty.subst σ₁ (.param 0) = forwarded f :=
    subst_param_type _ _ _ (by simp [σ₁, Bindings.lookup]) (forwarded_isType f hf)
  have h1 : Ty.subst σ₁ (.param 1) = forwarded x :=
    subst_param_type _ _ _ (by simp [σ₁, Bindings.lookup]) (forwarded_isType x hx)
  have h2 : Ty.subst σ₁ (.param 2) = .ref (.lookup tc x.ty.stripConst) := by
    simp [Ty.subst, σ₁, Bindings.lookup]
  have hparams : formAll env [Ty.subst σ₁ (.rref (.param 0)), Ty.subst σ₁ (.rref (.param 1))] =
      .ok [Ty.collapse (.rref (forwarded f)), Ty.collapse (.rref (forwarded x))] := by
    show formAll env [Ty.collapse (.rref (Ty.subst σ₁ (.param 0))),
      Ty.collapse (.rref (Ty.subst σ₁ (.param 1)))] = _
    rw [h0, h1]
    simp [formAll, form_formed env _ (collapse_rref_forwarded_formed f hfF hfr),
      form_formed env _ (collapse_rref_forwarded_formed x hxF hxr)]
  have hplist : parameterListStep env (fmapObject tc).head σ₁ = .ok σ₁ := rfl
  have hsat : Constraint.satisfied env.atomic σ₁ (.atomic "fmap_call" [.param 2, .param 0, .param 1]) =
      Constraint.atomicAnswer v := by
    rw [Constraint.satisfied_atomic]
    simp only [List.map, h0, h1, h2]
    rw [show [Ty.ref (.lookup tc x.ty.stripConst), forwarded f, forwarded x] = memberArgs tc f x from rfl, hv]
  have hnd : nonDependentStep env [(Ty.param 0).rref, (Ty.param 1).rref] [f, x] σ₁ = .ok σ₁ := rfl
  have hft : functionTypeStep env (fmapObject tc) σ₁ = .ok (fmapSpec tc f x) := by
    simp only [functionTypeStep, fmapObject, List.map]
    rw [hparams]
    rfl
  rw [hplist]
  simp only [Subst.bind_eq, Subst.bind_ok, constraintStep, fmapObject, hsat]
  cases v with
  | ok b =>
    cases b
    · simp [Constraint.atomicAnswer, memberOutcome]
    · simp only [Constraint.atomicAnswer, ↓reduceIte, Subst.pure_eq, Subst.bind_ok, hnd]
      exact hft
  | soft _ => simp [Constraint.atomicAnswer, memberOutcome]
  | hard _ => rfl

/-- The operation object adds nothing and loses nothing. Whatever the
member call through the instance answers, deducing the operation object
is that answer, once the lookup at the container's type has been
instantiated: a specialization where the member call is valid and true, a
deduction failure where it is not, and a hard error where checking it is
one. The environment is arbitrary, so this holds for any member, accurate
or not. -/
theorem fmapObject_member (env : Env) (v : Subst Bool)
    (hv : env.atomic "fmap_call" (memberArgs tc f x) = v)
    (hf : f.ty.isType = true) (hx : x.ty.isType = true)
    (hfF : f.ty.formed = true) (hxF : x.ty.formed = true)
    (hfr : f.ty.isRef = false) (hxr : x.ty.isRef = false) (hxd : x.ty.dependent = false) :
    deduceTemplate env (fmapObject tc) [] [f, x] =
      (env.instantiate tc x.ty.stripConst).bind fun _ => memberOutcome (fmapSpec tc f x) v := by
  have hs := fmapObject_rest_member tc f x env v hv hf hx hfF hxF hfr hxr
  simp only [Subst.bind_eq] at hs
  simp only [deduceTemplate]
  rw [fmapObject_call _ tc f x hf hx]
  simp only [Subst.bind_eq, Subst.bind_ok]
  rw [fmapObject_defaults tc f x _ hx hxF hxr hxd]
  cases env.instantiate tc x.ty.stripConst with
  | ok _ =>
    simp only [Subst.bind_ok]
    exact hs
  | soft _ => rfl
  | hard _ => rfl

/-- The three outcomes, once the lookup is instantiated. -/
theorem member_transfer (env : Env) (v : Subst Bool) (inst : Ty)
    (hv : env.atomic "fmap_call" (memberArgs tc f x) = v)
    (hi : env.instantiate tc x.ty.stripConst = .ok inst)
    (hf : f.ty.isType = true) (hx : x.ty.isType = true)
    (hfF : f.ty.formed = true) (hxF : x.ty.formed = true)
    (hfr : f.ty.isRef = false) (hxr : x.ty.isRef = false) (hxd : x.ty.dependent = false) :
    let r := deduceTemplate env (fmapObject tc) [] [f, x]
    (v = .ok true → r = .ok (fmapSpec tc f x)) ∧
    ((v = .ok false ∨ ∃ e, v = .soft e) → ∃ e, r = .soft e) ∧
    (∀ e, v = .hard e → r = .hard e) := by
  intro r
  have hd : r = _ := fmapObject_member tc f x env v hv hf hx hfF hxF hfr hxr hxd
  rw [hi] at hd
  simp only [Subst.bind_ok] at hd
  refine ⟨fun h => ?_, fun h => ?_, fun e h => ?_⟩
  · rw [hd, h]; rfl
  · rcases h with h | ⟨e, h⟩ <;> (rw [hd, h]; exact ⟨_, rfl⟩)
  · rw [hd, h]; rfl

/-- The encoding's environment is the accurate member: the member call is
valid and true exactly when the lookup selects an instance. The theorems
about the operation object in `Overload/Typeclass/Encoding.lean` are this
case. -/
theorem ofProgram_member (p : Program) :
    (encodingEnv p).atomic "fmap_call" (memberArgs tc f x) =
      .ok (p.selectInstance tc x.ty.stripConst).toOption.isSome := by
  simp [encodingEnv, Env.ofProgram, memberAtomics, memberArgs]

end member

/-! ## A member that is not accurate -/

/-- An environment whose member call answers `v` in place of the
program's. -/
def _root_.Overload.Env.withMember (env : Env) (v : Subst Bool) : Env :=
  { env with atomic := fun e args => if e = "fmap_call" then v else env.atomic e args }

/-- A unit with a Functor instance for `box<T>`, and the operation
object. -/
def memberProgram : Program :=
  [ .classTemplate "box" [{ kind := .type }], .lookup "functor"
  , .instance "functor" [{ kind := .type }] (.spec' "box" [.param 0])
  , .functionTemplate (fmapObject "functor") ]

/-- A member that is hard to check, as an unconstrained member with a
deduced return type is, makes the call of the operation object
ill-formed, though the lookup selects an instance and the instance is
the only candidate. The operation object cannot make the member
accurate. -/
theorem inaccurate_member_ill_formed (r : Ranking Conv) :
    ∃ e, resolve .text ((encodingEnv memberProgram).withMember (.hard "invoke_result has no type"))
      r (memberProgram.candidates "fmap")
      [{ ty := .named "not_callable", lvalue := false }, { ty := .spec' "box" [.named "int"], lvalue := false }] =
      .illFormed e :=
  resolve_text_hard _ r _ _ (fmapObject "functor") _ (by simp [memberProgram, Program.candidates, fmapObject])
    (by rfl)

/-- The same call with the accurate member is viable. -/
theorem accurate_member_selected :
    (resolve .text (encodingEnv memberProgram) memberProgram.ranking (memberProgram.candidates "fmap")
      [{ ty := .named "inc", lvalue := false }, { ty := .spec' "box" [.named "int"], lvalue := false }]).map
      (·.index) = .selected 0 := by
  rfl

/-! ## An operation object with several `operator()`s -/

/-- A second `operator()` on the operation object, as `fold_map_fn` and
`combine_all_fn` have: an explicit argument after the function and the
container, `template <class F, class T, class M, const auto &TC =
tc<std::remove_cvref_t<T>>> auto operator()(F &&, T &&, M) const`. The
lookup default comes after the parameter a two-argument call cannot
deduce. -/
def withExtraObject (tc : String) : FunctionTemplate :=
  { name := "fmap"
    head :=
      [ { kind := .type }, { kind := .type }, { kind := .type }
      , { kind := .const (.lref (.const (.named "auto")))
          default := some (.ref (.lookup tc (.removeCvref (.param 1)))) } ]
    params := [.rref (.param 0), .rref (.param 1), .param 2]
    constraint := some (.atomic "fmap_call" [.param 3, .param 0, .param 1, .param 2]) }

/-- The same `operator()` with the lookup default before the extra
parameter. -/
def withExtraObjectEarly (tc : String) : FunctionTemplate :=
  { name := "fmap"
    head :=
      [ { kind := .type }, { kind := .type }
      , { kind := .const (.lref (.const (.named "auto")))
          default := some (.ref (.lookup tc (.removeCvref (.param 1)))) }
      , { kind := .type } ]
    params := [.rref (.param 0), .rref (.param 1), .param 3]
    constraint := some (.atomic "fmap_call" [.param 2, .param 0, .param 1, .param 3]) }

section arity

variable (tc : String) (f x : CallArg)

theorem withExtraObject_call (env : Env) (hf : f.ty.isType = true) (hx : x.ty.isType = true) :
    (explicitStep env (withExtraObject tc).head [] >>= callStep env (withExtraObject tc).params [f, x]) =
      .ok [(1, forwarded x), (0, forwarded f)] := by
  have h0 : Ty.collapse (.rref (.param 0)) = .rref (.param 0) := rfl
  have h1 : Ty.collapse (.rref (.param 1)) = .rref (.param 1) := rfl
  have hl : ∀ t : Ty, (Ty.lref t).isType = true := fun _ => rfl
  cases hlf : f.lvalue <;> cases hlx : x.lvalue <;>
    simp [h0, h1, hl, withExtraObject, explicitStep, explicitStep.go, callStep, deduceCall, deduceParam,
      adjustP, adjustA, isForwardingRef, Ty.isRef, Ty.referred, Ty.dependent, Ty.subst, Bindings.lookup,
      deduceTy, bindArg, forwarded, hlf, hlx, hf, hx]

/-- A two-argument call of the longer `operator()` fails at the parameter
it cannot deduce, before the lookup default: whatever the environment,
so whatever the lookup would do. It never reaches the lookup. -/
theorem withExtraObject_short (env : Env) (hf : f.ty.isType = true) (hx : x.ty.isType = true) :
    deduceTemplate env (withExtraObject tc) [] [f, x] =
      .soft "template parameter 2 is neither deduced nor explicitly specified" := by
  simp only [deduceTemplate]
  rw [withExtraObject_call tc f x env hf hx]
  rfl

/-- Neither `operator()` reaches the lookup in a call of the other's
arity: the shorter fails at the call, the longer before its default. -/
theorem arity_disjoint_soft (env env' : Env) (m : CallArg) (hf : f.ty.isType = true) (hx : x.ty.isType = true) :
    deduceTemplate env' (withExtraObject tc) [] [f, x] = deduceTemplate env (withExtraObject tc) [] [f, x] ∧
    deduceTemplate env' (fmapObject tc) [] [f, x, m] = deduceTemplate env (fmapObject tc) [] [f, x, m] := by
  refine ⟨?_, ?_⟩
  · rw [withExtraObject_short tc f x env hf hx, withExtraObject_short tc f x env' hf hx]
  · rw [deduceTemplate_too_many env' _ _ (by simp [fmapObject]),
      deduceTemplate_too_many env _ _ (by simp [fmapObject])]

/-- Stability at the call surface for an operation object with both
`operator()`s. The hypothesis `call_stability` puts on the other
candidates is discharged: the other `operator()` does not reach the
lookup. -/
theorem call_stability_arity (p₁ p₂ : Program) (h : Head) (pat : Ty) (r : Ranking Conv)
    (hf : f.ty.isType = true) (hx : x.ty.isType = true)
    (hfF : f.ty.formed = true) (hxF : x.ty.formed = true)
    (hfr : f.ty.isRef = false) (hxr : x.ty.isRef = false) (hxd : x.ty.dependent = false)
    (hsoft : (p₁ ++ p₂).any (fun | .lookup c => c = tc | _ => false) = true)
    (hhard : (p₁ ++ p₂).any (fun | .lookupHard c => c = tc | _ => false) = false) :
    let decls := [Decl.functionTemplate (fmapObject tc), .functionTemplate (withExtraObject tc)]
    let p := p₁ ++ p₂
    let p' := p₁ ++ .instance tc h pat :: p₂
    resolve .text (encodingEnv p') r decls [f, x] = resolve .text (encodingEnv p) r decls [f, x] ∨
    (PatternMatches h pat x.ty.stripConst ∧
      (p'.selectInstance tc x.ty.stripConst = .selected (p₁.instancesOf tc).length ∨
        ∃ e, resolve .text (encodingEnv p') r decls [f, x] = .illFormed e)) := by
  intro decls p p'
  refine call_stability p₁ p₂ tc h pat r decls f x hf hx hfF hxF hfr hxr hxd hsoft hhard
    (by simp [decls]) fun ft hft hne => ?_
  simp only [decls, List.mem_cons, Decl.functionTemplate.injEq, List.not_mem_nil, or_false] at hft
  rcases hft with rfl | rfl
  · exact absurd rfl hne
  · exact (arity_disjoint_soft tc f x _ _ x hf hx).1

end arity

/-- Two instances for `box<T>`, neither more specialized than the other:
a lookup at `box<int>` is ambiguous. -/
def ambiguousProgram : Program :=
  [ .classTemplate "box" [{ kind := .type }], .lookup "functor"
  , .instance "functor" [{ kind := .type }] (.spec' "box" [.param 0])
  , .instance "functor" [{ kind := .type }] (.spec' "box" [.param 0]) ]

/-- The order matters when the object's other `operator()` does not
consult the lookup. A non-template `operator()` that takes the call's
arguments exactly sits beside the longer one. With the lookup default
last, the longer one fails before reaching the lookup, and the
non-template is selected though the lookup is ambiguous. With the lookup
default first, the longer one substitutes the ambiguous lookup, a hard
error, and under the text the call is ill-formed. -/
theorem arity_order_matters :
    let args := [{ ty := .named "not_callable", lvalue := false },
                 { ty := .spec' "box" [.named "int"], lvalue := false : CallArg }]
    let exact := Decl.function "fmap" [.named "not_callable", .spec' "box" [.named "int"]]
    (resolve .text (encodingEnv ambiguousProgram) ambiguousProgram.ranking
        [exact, .functionTemplate (withExtraObject "functor")] args).map (·.index) = .selected 0 ∧
    ∃ e, resolve .text (encodingEnv ambiguousProgram) ambiguousProgram.ranking
        [exact, .functionTemplate (withExtraObjectEarly "functor")] args = .illFormed e :=
  ⟨rfl, ⟨_, rfl⟩⟩



/-! ## An algorithm over an instance

An algorithm written against a typeclass takes an instance and calls its
members. To the model it is one more function template: its constraint
is what it states about those calls, and the member calls' answers come
from the environment, as the operation object's does. When the
constraint is the conjunction of the member calls the body makes, the
algorithm answers as its members do, call by call, in the order the
constraint writes them (`algorithm_transfer`). It is accurate when they
are (`algorithm_accurate`). The order is part of the answer: a call
written after one that is not satisfied is never checked, so a hard
error there does not count, and written first it does
(`call_order_matters`). Both theorems are the Standard side's
`conjunction_answers` and `conjunction_no_hard`, read for an algorithm.
-/

section algorithm

variable (env : Env) (a : Constraint.Atomic) (as : List Constraint.Atomic) (σ : Bindings)

/-- An algorithm whose constraint is the conjunction of its member calls
answers as its members do. Every call valid and true, the constraint step
passes. Otherwise the first call that is not decides: not valid or false,
a constraint not satisfied; a hard error, a hard error. Nothing the
algorithm adds changes a member's answer, and nothing a later call
answers is consulted. -/
theorem algorithm_transfer :
    let r := constraintStep env (some (conjunctionOf a as)) σ
    let vs := answers env.atomic σ (a :: as)
    ((∀ v ∈ vs, v = .ok true) → r = .ok σ) ∧
    (∀ pre v post, vs = pre ++ v :: post → (∀ u ∈ pre, u = .ok true) →
      (v = .ok false ∨ ∃ e, v = .soft e) → ∃ e, r = .soft e) ∧
    (∀ pre e post, vs = pre ++ .hard e :: post → (∀ u ∈ pre, u = .ok true) → r = .hard e) :=
  conjunction_answers env a as σ

/-- Accurate members make an accurate algorithm. When no member call is
a hard error to check, neither is the algorithm's constraint: a call of
it is viable so far or a constraint not satisfied. -/
theorem algorithm_accurate (h : ∀ v ∈ answers env.atomic σ (a :: as), ∀ e, v ≠ .hard e) :
    ∀ e, constraintStep env (some (conjunctionOf a as)) σ ≠ .hard e :=
  conjunction_no_hard env a as σ h

end algorithm

/-- Two member calls, one not satisfied and one a hard error to check.
Written with the unsatisfied call first, the algorithm is a constraint not
satisfied, and the hard error is never reached; written the other way,
the algorithm is a hard error. This is why the folds test for a
registered `Monoid` before they name one. -/
def orderEnv : Env :=
  { encodingEnv [] with
    atomic := fun e _ =>
      if e = "registered" then .ok false else if e = "combine_call" then .hard "Monoid<V> is incomplete"
      else .ok true }

theorem call_order_matters :
    constraintStep orderEnv (some (conjunctionOf ("registered", []) [("combine_call", [])])) [] =
      .soft "associated constraints not satisfied" ∧
    constraintStep orderEnv (some (conjunctionOf ("combine_call", []) [("registered", [])])) [] =
      .hard "Monoid<V> is incomplete" := by
  constructor <;> rfl


end Overload.Typeclass
