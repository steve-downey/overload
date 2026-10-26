-- Overload/Typeclass/Derivation.lean                                 -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Typeclass.Encoding
import Overload.ClassTemplates

/-!
# The derivation base, and the operation object's constraint resolved

beman.transpose's derivation base is a class template, `template <class
Impl> struct derive_functor : protected Impl`, whose member templates
`fmap` and `replace` are constrained by requires-expressions over
`Impl` (`src/smd/overload/encoding.hpp`), and an instance's value is a
specialization of it. The model declared the base as a plain class where
it needed the name, and answered the operation object's constraint,
`TC.fmap(declval<F>(), declval<T>())`, by an oracle that says true
exactly when the lookup selects an instance (`memberAtomics`). With
class template members the base is declared as it is (`deriveFunctor`),
an instance declares the type of its value (`Decl.instance`), and the
operation object's constraint is the requires-expression the header
writes (`fmapResolved`), resolved as the member call on the value's type.

* `operation_constraint_is_member_call`: the resolved constraint holds,
  in the environment one level up, exactly where the member call `fmap`
  on the type the selected instance declares its value to have is viable
  and well-formed, the object an lvalue of `const` that type. The oracle
  assumed that; the environment computes it.
* `derivation_base_accurate`: the constraint of `derive_functor<Impl>::fmap`
  holds exactly where `Impl`'s `fmap` is viable on a `const Impl&` with
  the deduced arguments. The requires-clause is the call the body makes,
  so a probe of `fmap` through the base fails softly exactly where the
  implementation's member is not viable: the accurate-members obligation
  holds by construction for the reduced header.
* `resolved_operation_example`, `inaccurate_oracle_example`: on an
  instance whose implementation's `fmap` takes `(Fn, box<int>)`, the
  resolved operation object is viable at `(Fn, box<int>)` and not at
  `(int, box<int>)`, where the oracle, true whenever an instance is
  selected, would have said it was.
* `unconstrained_member_hides_derivation_base`: an instance type derived
  from `derive_functor<Impl>` that declares its own `fmap` hides the
  constrained one, on the real shape of the audit's finding.

`memberAtomics` stays as the specification of the abstract operation
object, which the theorems of `Overload/Typeclass/Encoding.lean` and
`Overload/Typeclass/Members.lean` are about; the resolved object is the
header's, and the two agree where the implementation's member is
accurate.
-/

namespace Overload.Typeclass

private def tp : TemplateParam := { kind := .type }

/-- `template <class VALUE> struct constant_function { VALUE value;
template <class ARGUMENT> constexpr VALUE operator()(const ARGUMENT&)
const; };`, the function `replace` maps with. -/
def constantFunction : Program :=
  [ .classTemplate "constant_function" [tp]
  , .member (currentInstantiation "constant_function" [tp]) { name := "value", ty := .param 0 }
  , .functionTemplate { name := "operator()", head := [tp], params := [.lref (.const (.param 1))]
                        ret := .param 0, scope := [.class "constant_function"] } ]

/-- `template <class FUNCTION, class T> auto fmap(FUNCTION&&, T&&) const
requires requires(const Impl& impl) { impl.fmap(forward<FUNCTION>(f),
forward<T>(v)); }`: `Impl` is the class's parameter, `.param 0`, and the
member's own follow it. -/
def deriveFmap : FunctionTemplate :=
  { name := "fmap", head := [tp, tp], params := [.rref (.param 1), .rref (.param 2)]
    constraint := some (.requires [.memberCall (.lref (.const (.param 0))) "fmap" [.param 1, .param 2]]
      [.param 0, .param 1, .param 2])
    scope := [.class "derive_functor"] }

/-- `template <class T, class U> auto replace(T&&, U&&) const requires
requires(const Impl& impl) { impl.replace(...); } || requires(const Impl&
impl) { impl.fmap(constant_function<remove_cvref_t<U>>{...}, ...); }`. -/
def deriveReplace : FunctionTemplate :=
  { name := "replace", head := [tp, tp], params := [.rref (.param 1), .rref (.param 2)]
    constraint := some (.disj
      (.requires [.memberCall (.lref (.const (.param 0))) "replace" [.param 1, .param 2]]
        [.param 0, .param 1, .param 2])
      (.requires [.memberCall (.lref (.const (.param 0))) "fmap"
          [.spec' "constant_function" [.removeCvref (.param 2)], .param 1]]
        [.param 0, .param 1, .param 2]))
    scope := [.class "derive_functor"] }

/-- The derivation base as the header declares it: `template <class Impl>
struct derive_functor : protected Impl`, with `fmap` and `replace`. -/
def deriveFunctor : Program :=
  constantFunction ++
    [ .classTemplate "derive_functor" [tp] [] [.param 0]
    , .functionTemplate deriveFmap, .functionTemplate deriveReplace ]

/-- The operation object with its constraint as the header writes it,
`requires { TC.fmap(std::declval<FUNCTION>(), std::declval<T>()); }`: a
member call on the lookup's value, which the environment resolves. -/
def fmapResolved (tc : String) : FunctionTemplate :=
  { fmapObject tc with
    constraint := some (.requires
      [.memberCall (.lref (.const (.typeOf (.param 2)))) "fmap" [.param 0, .param 1]]
      [.param 2, .param 0, .param 1]) }

/-! ## The resolved constraint is the member call -/

/-- A requires-expression of one requirement is satisfied one level up
exactly where the requirement, with the bindings substituted, holds one
level down. -/
theorem satisfied_requires_singleton_iff (p : Program) (atomics : List (String × List Ty × Bool))
    (extra : Constraint.ExprOracle) (traits : Trait → List Ty → Subst Bool) (depth : Nat)
    (σ : Bindings) (r : Constraint.Requirement) (m : List Ty) :
    Constraint.satisfied (Env.fullWithin p atomics extra traits (depth + 1)).atomic σ (.requires [r] m) =
        .ok true ↔
      p.requirementHolds (Env.fullWithin p atomics extra traits depth) (r.subst σ) = .ok true := by
  rw [Constraint.satisfied_requires]
  show Constraint.atomicAnswer (p.requirementsHold _ [r.subst σ]) = .ok true ↔ _
  simp only [Program.requirementsHold]
  cases h : p.requirementHolds (Env.fullWithin p atomics extra traits depth) (r.subst σ) with
  | ok b => cases b <;> simp [Constraint.atomicAnswer]
  | soft e => simp [Constraint.atomicAnswer]
  | hard e => simp [Constraint.atomicAnswer]

/-- The bindings the operation object has after deducing `F` and `T` and
taking the lookup as its default: the same as `fmapSpec` records. -/
def resolvedBindings (tc : String) (f x : CallArg) : Bindings :=
  [(2, .ref (.lookup tc x.ty.stripConst)), (1, forwarded x), (0, forwarded f)]

/-- The operation object's constraint, resolved: with `TC` bound to the
lookup at the container's type and `F`, `T` deduced, the
requires-expression holds in the environment one level up exactly where
the member call `fmap` on the type the selected instance declares its
value to have, an lvalue of `const` that type, with the forwarded
arguments, is viable and well-formed one level down. -/
@[std theorem "expr.prim.req.simple#1" "over.match.funcs.general#3" "temp.deduct.general#5"]
theorem operation_constraint_is_member_call (p : Program) (atomics : List (String × List Ty × Bool))
    (extra : Constraint.ExprOracle) (traits : Trait → List Ty → Subst Bool) (depth : Nat)
    (tc : String) (f x : CallArg) (v : Ty) (hf : f.ty.isType = true) (hx : x.ty.isType = true)
    (hv : p.instanceValueType? tc x.ty.stripConst = some v) (hc : v.isClass = true)
    (hkd : x.ty.stripConst.dependent = false)
    (hfa : form (Env.fullWithin p atomics extra traits depth) x.ty.stripConst = .ok x.ty.stripConst)
    (hinst : ∃ t, (Env.fullWithin p atomics extra traits depth).instantiate tc x.ty.stripConst = .ok t)
    (hargs : formAll (Env.fullWithin p atomics extra traits depth) [forwarded f, forwarded x] =
      .ok [forwarded f, forwarded x])
    (hgen : ∀ ms, p.memberSearch p.length v "fmap" = .selected ms →
      ∀ r, generate .text (Env.fullWithin p atomics extra traits depth)
        (((entities ms).map (Decl.withImplicitObject v)).map p.normalizeDecl)
        (impliedObject v :: [forwarded f, forwarded x].map Program.declval) [] ≠ .hard r) :
    Constraint.satisfied (Env.fullWithin p atomics extra traits (depth + 1)).atomic (resolvedBindings tc f x)
        (.requires [.memberCall (.lref (.const (.typeOf (.param 2)))) "fmap" [.param 0, .param 1]]
          [.param 2, .param 0, .param 1]) = .ok true ↔
      ∃ cand, p.memberCallOn (Env.fullWithin p atomics extra traits depth) p.length v (impliedObject v) "fmap"
        [Program.declval (forwarded f), Program.declval (forwarded x)] = .selected cand := by
  rw [satisfied_requires_singleton_iff]
  have h0 : Ty.subst (resolvedBindings tc f x) (.param 0) = forwarded f :=
    subst_param_type _ _ _ (by simp [resolvedBindings, Bindings.lookup]) (forwarded_isType f hf)
  have h1 : Ty.subst (resolvedBindings tc f x) (.param 1) = forwarded x :=
    subst_param_type _ _ _ (by simp [resolvedBindings, Bindings.lookup]) (forwarded_isType x hx)
  have h2 : Ty.subst (resolvedBindings tc f x) (.lref (.const (.typeOf (.param 2)))) =
      .lref (.const (.typeOf (.ref (.lookup tc x.ty.stripConst)))) := by
    simp [Ty.subst, resolvedBindings, Bindings.lookup, Ty.collapse]
  simp only [Constraint.Requirement.subst, List.map, h0, h1, h2]
  exact lookup_member_requirement_iff_call p _ tc x.ty.stripConst v "fmap" [forwarded f, forwarded x]
    hv hc hkd hfa hinst hargs hgen

/-! ## The derivation base is accurate -/

/-- `derive_functor<Impl>::fmap` for a class `Impl`: the class's parameter
substituted, the member's own renumbered from zero, the constraint the
member call on `const Impl&`. -/
theorem deriveFmap_instantiate (n : String) :
    Decl.instantiate [.named n] (.functionTemplate deriveFmap) =
      .functionTemplate
        { name := "fmap", head := [tp, tp], params := [.rref (.param 0), .rref (.param 1)]
          constraint := some (.requires [.memberCall (.lref (.const (.named n))) "fmap" [.param 0, .param 1]]
            [.named n, .param 0, .param 1])
          scope := [.class "derive_functor"] } := by
  rfl

/-- The constraint of `derive_functor<Impl>::fmap<F, T>` holds one level
up exactly where the member call `fmap` on a `const Impl&` with
`declval<F>()` and `declval<T>()` is viable and well-formed one level
down: the requires-clause is the call the body makes. -/
@[std theorem "expr.prim.req.simple#1" "temp.constr.decl#1"]
theorem derivation_base_accurate (p : Program) (atomics : List (String × List Ty × Bool))
    (extra : Constraint.ExprOracle) (traits : Trait → List Ty → Subst Bool) (depth : Nat)
    (n : String) (F T : Ty) (hn : (Ty.named n).isClass = true) (hF : F.isType = true) (hT : T.isType = true)
    (hFf : form (Env.fullWithin p atomics extra traits depth) F = .ok F)
    (hTf : form (Env.fullWithin p atomics extra traits depth) T = .ok T)
    (hgen : ∀ ms, p.memberSearch p.length (.named n) "fmap" = .selected ms →
      ∀ r, generate .text (Env.fullWithin p atomics extra traits depth)
        (((entities ms).map (Decl.withImplicitObject (.named n))).map p.normalizeDecl)
        (impliedObject (.named n) :: [F, T].map Program.declval) [] ≠ .hard r) :
    Constraint.satisfied (Env.fullWithin p atomics extra traits (depth + 1)).atomic [(1, T), (0, F)]
        (.requires [.memberCall (.lref (.const (.named n))) "fmap" [.param 0, .param 1]]
          [.named n, .param 0, .param 1]) = .ok true ↔
      ∃ cand, p.memberCallOn (Env.fullWithin p atomics extra traits depth) p.length (.named n)
        (impliedObject (.named n)) "fmap" [Program.declval F, Program.declval T] = .selected cand := by
  rw [satisfied_requires_singleton_iff]
  have h0 : Ty.subst [(1, T), (0, F)] (.param 0) = F :=
    subst_param_type _ _ _ (by simp [Bindings.lookup]) hF
  have h1 : Ty.subst [(1, T), (0, F)] (.param 1) = T :=
    subst_param_type _ _ _ (by simp [Bindings.lookup]) hT
  have h2 : Ty.subst [(1, T), (0, F)] (.lref (.const (.named n))) = .lref (.const (.named n)) := by
    simp [Ty.subst, Ty.collapse]
  simp only [Constraint.Requirement.subst, List.map, h0, h1, h2]
  refine member_requirement_iff_call p _ (.lref (.const (.named n))) "fmap" [F, T] ?_ ?_ rfl rfl hn hgen
  · simp [form, formConst, Ty.collapse, Ty.isRef]
  · simp [formAll, hFf, hTf]

/-! ## On a program -/

/-- An instance whose implementation's `fmap` takes `(Fn, box<int>)` by
value, and one whose `fmap` is a member template over the function
and takes `list<int>`; each instance declares its value's type, a
specialization of the derivation base; and the operation object with
its constraint resolved. -/
def deriveExample : Program :=
  deriveFunctor ++
    [ .class "Fn", .classTemplate "box" [tp], .classTemplate "list" [tp]
    , .class "box_impl"
    , .function "fmap" [.named "Fn", .spec' "box" [.named "int"]] [.class "box_impl"] .none none
        (.spec' "box" [.named "int"])
    , .class "list_impl"
    , .functionTemplate { name := "fmap", head := [tp], params := [.rref (.param 0), .spec' "list" [.named "int"]]
                          ret := .spec' "list" [.named "int"], scope := [.class "list_impl"] }
    , .lookup "functor"
    , .instance "functor" [tp] (.spec' "box" [.param 0]) (some (.spec' "derive_functor" [.named "box_impl"]))
    , .instance "functor" [tp] (.spec' "list" [.param 0]) (some (.spec' "derive_functor" [.named "list_impl"]))
    , .functionTemplate (fmapResolved "functor") ]

private def env : Env := Env.full deriveExample
private def fn : CallArg := { ty := .named "Fn" }
private def boxInt : CallArg := { ty := .spec' "box" [.named "int"] }
private def listInt : CallArg := { ty := .spec' "list" [.named "int"] }

/-- The selected instance's value is `derive_functor<box_impl>`. -/
theorem instance_value_example :
    deriveExample.instanceValueType? "functor" (.spec' "box" [.named "int"]) =
      some (.spec' "derive_functor" [.named "box_impl"]) ∧
    deriveExample.instanceValueType? "functor" (.named "int") = none := by
  refine ⟨by decide, by decide⟩

/-- The resolved operation object is viable at `(Fn, box<int>)`, where
`box_impl::fmap` is, and at `(int, list<int>)`, where `list_impl`'s
member template is. -/
theorem resolved_operation_example :
    (deriveExample.callAt env deriveExample.length [] "fmap" [fn, boxInt]).map (·.index) = .selected 0 ∧
    (deriveExample.callAt env deriveExample.length [] "fmap" [{ ty := .named "int" }, listInt]).map (·.index) =
      .selected 0 := by
  refine ⟨by decide, by decide⟩

/-- At `(int, box<int>)` the lookup selects the `box` instance, so the
oracle of the abstract operation object says the constraint holds; the
resolved one is not viable, since `box_impl::fmap` takes an `Fn`. And at
`(Fn, int)` no instance is selected, and neither is viable. -/
theorem inaccurate_oracle_example :
    (deriveExample.callAt env deriveExample.length [] "fmap" [{ ty := .named "int" }, boxInt]).map (·.index) =
      .noMatch ∧
    memberAtomics deriveExample "fmap_call"
      [.ref (.lookup "functor" (.spec' "box" [.named "int"])), .named "int", .spec' "box" [.named "int"]] = .ok true ∧
    (deriveExample.callAt env deriveExample.length [] "fmap" [fn, { ty := .named "int" }]).map (·.index) =
      .noMatch := by
  refine ⟨by decide, by decide, by decide⟩

/-- `replace` through `fmap` with `constant_function`: viable on
`derive_functor<list_impl>` at `(list<int>, int)`, whose `fmap` takes any
function, and not on `derive_functor<box_impl>` at `(box<int>, int)`,
whose `fmap` takes an `Fn`. -/
theorem replace_through_fmap_example :
    (deriveExample.memberCallAt env deriveExample.length (.spec' "derive_functor" [.named "list_impl"]) "replace"
      [listInt, { ty := .named "int" }]).map (·.index) = .selected 0 ∧
    (deriveExample.memberCallAt env deriveExample.length (.spec' "derive_functor" [.named "box_impl"]) "replace"
      [boxInt, { ty := .named "int" }]).map (·.index) = .noMatch := by
  refine ⟨by decide, by decide⟩

/-- An instance type derived from the base that declares its own `fmap`,
unconstrained: the shape the audit found in the library's Functor
instances, on the real derivation base. -/
def hidingDerivedProgram : Program :=
  deriveExample ++
    [ .class "box_monad" [.spec' "derive_functor" [.named "box_impl"]]
    , .functionTemplate { name := "fmap", head := [tp, tp], params := [.rref (.param 0), .rref (.param 1)]
                          scope := [.class "box_monad"] } ]

/-- The search for `fmap` in `box_monad` finds its own and nothing from
the base, so a probe of the member through the instance type resolves
over the unconstrained one at `(int, box<int>)`, where the base's would
have refused. -/
@[std theorem "class.member.lookup#3"]
theorem unconstrained_member_hides_derivation_base :
    hidingDerivedProgram.memberSearch hidingDerivedProgram.length (.named "box_monad") "fmap" =
      .selected [.functionTemplate { name := "fmap", head := [tp, tp], params := [.rref (.param 0), .rref (.param 1)]
                                     scope := [.class "box_monad"] }] ∧
    (hidingDerivedProgram.memberCallAt (Env.full hidingDerivedProgram) hidingDerivedProgram.length
      (.named "box_monad") "fmap" [{ ty := .named "int" }, boxInt]).map (·.index) = .selected 0 := by
  refine ⟨by decide, by decide⟩

end Overload.Typeclass
