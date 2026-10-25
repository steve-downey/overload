-- Overload/Typeclass/Conversion.lean                                 -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Typeclass.Routes
import Overload.Typeclass.Arguments

/-!
# A conversion between instance types

The other way to write refinement in the type system, beside deriving
one instance type from another, is a user-defined conversion from the
stronger instance type to the weaker: a Monad instance that converts to
an Applicative instance. The encoding has none, and takes instances at
their deduced type. What a conversion would cost, with the Standard
side's user-defined conversion sequences (`Overload/Ranking.lean`):

* `conversion_invisible_to_deduction`: a generic algorithm deduces the
  Monad instance type and resolves exactly as it would without the
  conversion. Deduction never applies a user-defined conversion
  ([temp.deduct.call]/4), so the conversion fires at no deduced
  parameter, which is every generic algorithm.
* `conversion_loses_rank`: beside an overload naming the Applicative
  instance type, the generic template wins at the Monad instance type,
  since a standard conversion sequence beats a user-defined one
  ([over.ics.rank]/2) before the non-template preference is reached.
  Leak 1 of inheritance again, with a worse conversion.
* `converting_sites_ambiguous`: two overloads naming two instance types
  the third converts to are indistinguishable at it ([over.ics.rank]/3).
* `converted_instance_temporary`: the result of a conversion is a
  prvalue. Pinning it is a deduction failure, since the reference
  parameter would bind a temporary ([temp.arg.nontype]/6); and under
  the typed value route every instance value that converts to the
  parameter's class names one specialization
  (`value_route_identifies_converted`), as slicing does.
* `explicit_conversion_dead`: with the conversion explicit, no call
  forms it: argument passing is copy-initialization, for which an
  explicit conversion is no candidate ([over.match.copy]/1).

The encoding's refinement is a concept on the instance's shape and a
retrieval function, so none of this arises; the obligation is in
`obligations.md`.
-/

namespace Overload.Typeclass

/-- `template <class T> void use(const T&)`. -/
def genericUse : FunctionTemplate :=
  { name := "use", head := [{ kind := .type }], params := [.lref (.const (.param 0))] }

/-- An Applicative instance type and a Monad instance type, unrelated by
derivation, with a conversion function from the second to the first; a
generic `use(const T&)` and one that names the Applicative instance
type. -/
def conversionLeak : Program :=
  [ .class "applicative_i", .class "monad_i"
  , .converting (.named "monad_i") (.function (.named "applicative_i"))
  , .functionTemplate genericUse
  , .function "use" [.lref (.const (.named "applicative_i"))] ]

/-- The same program without the conversion. -/
def conversionLeakFree : Program :=
  conversionLeak.filter fun | .converting .. => false | _ => true

/-- A Monad instance, an lvalue. -/
def monadInstance : CallArg := { ty := .named "monad_i", lvalue := true }

/-- The generic algorithm deduces the Monad instance type for its
parameter, and deduces exactly what it does in the program without the
conversion: deduction never applies a user-defined conversion. -/
@[std theorem "temp.deduct.call#4"]
theorem conversion_invisible_to_deduction :
    (deduceTemplate (Env.ofProgram conversionLeak) genericUse [] [monadInstance]).map
        (·.args) = .ok [(0, .named "monad_i")] ∧
      deduceTemplate (Env.ofProgram conversionLeak) genericUse [] [monadInstance] =
        deduceTemplate (Env.ofProgram conversionLeakFree) genericUse [] [monadInstance] := by
  constructor <;> rfl

/-- At the Applicative instance type the overload naming it wins the tie,
as a non-template. At the Monad instance type the generic template wins:
its identity conversion beats the user-defined sequence before the
non-template preference is consulted. The conversion moves no call to
the overload it was written for. -/
@[std theorem "over.ics.rank#2"]
theorem conversion_loses_rank :
    (resolve .text (Env.ofProgram conversionLeak) conversionLeak.ranking
        (conversionLeak.candidates "use")
        [{ ty := .named "applicative_i", lvalue := true }]).map (·.index) = .selected 1 ∧
      (resolve .text (Env.ofProgram conversionLeak) conversionLeak.ranking
        (conversionLeak.candidates "use") [monadInstance]).map (·.index) = .selected 0 := by
  constructor <;> rfl

/-- Two instance types a third converts to, and an overload naming each. -/
def conversionSites : Program :=
  [ .class "applicative_i", .class "functor_i", .class "monad_i"
  , .converting (.named "monad_i") (.function (.named "applicative_i"))
  , .converting (.named "monad_i") (.function (.named "functor_i"))
  , .function "use" [.lref (.const (.named "applicative_i"))]
  , .function "use" [.lref (.const (.named "functor_i"))] ]

/-- At the Monad instance type the two overloads are reached by two
different conversions, which are indistinguishable, and the call is
ambiguous. -/
@[std theorem "over.ics.rank#3"]
theorem converting_sites_ambiguous :
    (resolve .text (Env.ofProgram conversionSites) conversionSites.ranking
        (conversionSites.candidates "use") [monadInstance]).map (·.index) = .ambiguous [0, 1] := by
  rfl

/-- Pinning a value, which is what a conversion yields, is a deduction
failure of the pinning template: its instance parameter is a reference,
which would bind a temporary. The converted instance has no object to
pin. -/
@[std theorem "temp.arg.nontype#6"]
theorem converted_instance_temporary (env : Env) (tc name : String) (c : Ty) (v : Val)
    (hc : c.isType = true) :
    ∃ r, explicitStep env (pinTemplate tc name).head [c, .value v] = .soft r := by
  obtain ⟨r, hr⟩ := placeholder_reference_refuses_value env.initializer [(0, c)] v
  refine ⟨r, ?_⟩
  have hv : (Ty.value v).isType = false := rfl
  simp [explicitStep, explicitStep.go, pinTemplate, kindMatches, hc, hv, hr]

/-- Under the typed value route, two instance values of other classes
that each convert to the parameter's class name one specialization when
the class has one value, as the library's member-less instance types do:
the candidate initializer is that value whichever constructor made it. A
conversion between instance types identifies the instances it converts,
as slicing does. -/
@[std theorem "temp.type#1"]
theorem value_route_identifies_converted (p : Program) (env : Env) (b d₁ d₂ : String) (vs₁ vs₂ w : Val)
    (args : List CallArg) (he : env.initializer = p.candidateInitializer)
    (hu : p.uniqueValue (.named b) = some w)
    (hp : (Ty.named b).hasPlaceholder = false) (hb : isInteger b = false)
    (hne₁ : b ≠ d₁) (hne₂ : b ≠ d₂)
    (h₁ : ∃ f v s, p.ics .copy { ty := .named d₁ } (.named b) = some (.userDefined f v s))
    (h₂ : ∃ f v s, p.ics .copy { ty := .named d₂ } (.named b) = some (.userDefined f v s)) :
    deduceTemplate env (valueRouteAt b) [.value (.obj d₁ vs₁)] args =
      deduceTemplate env (valueRouteAt b) [.value (.obj d₂ vs₂)] args := by
  have h := conversion_identifies p env b d₁ d₂ vs₁ vs₂ w valueRoute.head.tail [] he hu hp hb hne₁ hne₂ h₁ h₂
  unfold sameSpecialization at h
  unfold deduceTemplate
  rw [show (valueRouteAt b).head = { kind := .const (.named b) } :: valueRoute.head.tail from rfl, h]

/-- The conversion made explicit, with only the overload naming the
Applicative instance type. -/
def conversionExplicit : Program :=
  [ .class "applicative_i", .class "monad_i"
  , .converting (.named "monad_i") (.function (.named "applicative_i") true)
  , .function "use" [.lref (.const (.named "applicative_i"))] ]

/-- An explicit conversion is no candidate for the copy-initialization
that argument passing is, so no call forms it: the overload is not
viable at the Monad instance type. -/
@[std theorem "over.match.copy#1"]
theorem explicit_conversion_dead :
    (resolve .text (Env.ofProgram conversionExplicit) conversionExplicit.ranking
        (conversionExplicit.candidates "use") [monadInstance]).map (·.index) = .noMatch := by
  rfl

end Overload.Typeclass
