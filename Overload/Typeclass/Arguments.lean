-- Overload/Typeclass/Arguments.lean                                  -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Identity
import Overload.Typeclass.Routes

/-!
# The encoding's constant parameters and their conversion

Leak 4 of instance inheritance, as a theorem, and what closes it. The
plan's value route passes an instance as a constant template argument.
With that parameter typed as the instance class, a derived instance
value is sliced to the base subobject and names the specialization the
base's own value names (`value_route_slices`), so an algorithm pinned to
the derived instance runs the base's. The library's parameters are
references to the lookup variables: the parameter denotes the object, and
pinning a derived instance and pinning the base are different
specializations (`pin_keeps_identity`, the explicit-step half of
`superclass_identity`).

The value route is closed to the library's instance types for another
reason: a derivation base keeps the implementation as a protected base,
so neither it nor a class derived from it is structural, and neither can
be a template argument for a placeholder parameter at all
(`value_route_needs_structural`).
-/

namespace Overload.Typeclass

/-- The value route with its instance parameter typed as the instance
class `b` rather than `auto`: `template <b TC, class F, class T> requires
fmap_shape<std::remove_cvref_t<decltype(TC)>> void fmap(F &&, T &&)`. -/
def valueRouteAt (b : String) : FunctionTemplate :=
  { valueRoute with head := { kind := .const (.named b) } :: valueRoute.head.tail }

/-- Under the typed value route, a derived instance value and the base's
own value deduce the same specialization, whatever the call's
arguments: the derived instance is sliced. -/
theorem value_route_slices (env : Env) (b d : String) (vs ws : Val) (args : List CallArg)
    (hp : (Ty.named b).hasPlaceholder = false) (hb : isInteger b = false) (hne : b ≠ d)
    (hs : env.initializer (.named b) (.obj d vs) = some (.obj b ws)) :
    deduceTemplate env (valueRouteAt b) [.value (.obj d vs)] args =
      deduceTemplate env (valueRouteAt b) [.value (.obj b ws)] args := by
  have h := slicing_identifies env b d vs ws valueRoute.head.tail [] hp hb hne hs
  unfold sameSpecialization at h
  unfold deduceTemplate
  rw [show (valueRouteAt b).head = { kind := .const (.named b) } :: valueRoute.head.tail from rfl, h]

/-- Pinning two different objects, a derived instance and the base's, are
two specializations of the pinned template: the reference parameter
denotes the object. -/
theorem pin_keeps_identity (env : Env) (tc name o₁ o₂ : String) (c : Ty) (hc : c.isType = true)
    (hne : o₁ ≠ o₂) :
    ¬ sameSpecialization env (pinTemplate tc name).head [c, .ref (.named o₁)] [c, .ref (.named o₂)] := by
  intro h
  unfold sameSpecialization at h
  have hr : ∀ t : Ty, (Ty.ref t).isType = false := fun _ => rfl
  have hcv : ∀ r : Ty, convertArg env.initializer [(0, c)] (.const (.lref (.const (.named "auto"))))
      (.ref r) = .ok (.ref r) := fun r => convertArg_auto_ref _ _ _ rfl
  simp [explicitStep, explicitStep.go, pinTemplate, kindMatches, hc, hr, hcv] at h
  exact hne h

/-- The library's shape: a derivation base that keeps the implementation
as a protected base, and an instance type derived from it. -/
def protectedBaseInstances : Program :=
  [ .class "impl", .class "derive_functor" [] [.named "impl"]
  , .class "opt_functor" [.named "derive_functor"] ]

/-- Neither the derivation base nor the instance type is structural, so
neither can be the value route's argument; the implementation on its
own could. -/
theorem value_route_needs_structural :
    protectedBaseInstances.structural (.named "derive_functor") = false ∧
      protectedBaseInstances.structural (.named "opt_functor") = false ∧
      protectedBaseInstances.placeholderArgumentsPermitted valueRoute.head
        [.value (.obj' "opt_functor" [.obj' "derive_functor" [.obj' "impl" []]])] = false ∧
      protectedBaseInstances.placeholderArgumentsPermitted valueRoute.head
        [.value (.obj' "impl" [])] = true := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end Overload.Typeclass
