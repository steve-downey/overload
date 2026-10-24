-- Overload/Typeclass/Emit.lean                                       -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Emit
import Overload.Typeclass.Inheritance
import Overload.Typeclass.Units
import Overload.Typeclass.Members
import Overload.Typeclass.Lookup
import Overload.Typeclass.Conversion
import Overload.Typeclass.ValueNature
import Overload.Typeclass.Laws
import Overload.Typeclass.Arguments

/-!
# The emitted cases of the encoding

The differential cases whose programs are the typeclass encoding's: the
operation object of beman.transpose, the pinning pattern and the by-value
route, the plan's three routes as an alternative design, and the
inheritance leaks. They use the emitter of `Overload/Emit.lean` with a
prelude of their own: a `selected<K>` that has the operation, so that a
partial specialization's value is an instance, the instance object a user
pins, and the concepts the encoding's atomic constraints name.

Their expectations are computed in the encoding's environment
(`encodingEnv`), which `OverloadTest/Emit.lean` checks as it does the
Standard side's.
-/

namespace Overload.Typeclass.Emit

open Overload.Emit
open _root_.Overload.Std (Citation)

/-- The encoding's fixtures: an instance has `fmap`, the pinned instance
object has it too, `fmap_shape` is the shape constraint of the by-value
route, and `fmap_call` is the operation object's constraint, the call
through the instance. -/
def prelude : String :=
  "template <int K> struct selected {\n" ++
  "    template <class F, class X> static void fmap(F&&, X&&);\n};\n" ++
  "struct pinned_instance {\n" ++
  "    template <class F, class X> static void fmap(F&&, X&&);\n};\n" ++
  "template <class P> concept fmap_shape = requires(const P &p) { p.fmap(0, 0); };\n" ++
  "template <const auto &TC, class F, class X>\n" ++
  "concept fmap_call = requires { TC.fmap(std::declval<F>(), std::declval<X>()); };\n"

/-- A citation, for the case list. -/
private def cite (s : String) : Citation :=
  match Std.parseCitation s with
  | .ok c => c
  | .error _ => default

private def T : Ty := .param 0
private def int : Ty := .named "int"
private def typeParam : TemplateParam := { kind := .type }

/-! ### The operation object of beman.transpose

`fmap` as the library spells it: the container type is deduced from the
second argument, and the instance arrives through a trailing `const auto &`
constant template parameter defaulted to the lookup at the container's
type with cv and reference removed. The constraint is the call through the
instance. -/

private def opObject : FunctionTemplate := fmapObject "functor"

private def opProgram (extra : Program := []) (after : Program := []) : Program :=
  [ .class "Fn", .classTemplate "box" [typeParam], .classTemplate "pair" [typeParam, typeParam]
  , .lookup "functor", .instance "functor" [typeParam] (.spec' "box" [T]) ] ++ extra ++
  [ .functionTemplate opObject ] ++ after

private def fn : CallArg := { ty := .named "Fn" }

/-- The instance is found at the container's type. -/
def opObjectSelects : Case :=
  { name := "op_object_selects"
    cite := cite "temp.deduct.general#5.sentence-3"
    program := opProgram
    query := .call "fmap" [fn, { ty := .spec' "box" [int] }] (.selected 0)
    source := "computed by resolve"
    prelude := prelude }

/-- A const lvalue argument deduces `T` as `const box<int>&`, and the
lookup key is still `box<int>`: the normalized-key obligation, discharged
by `remove_cvref_t`. -/
def opObjectNormalizedKey : Case :=
  { name := "op_object_normalized_key"
    cite := cite "temp.deduct.call#3.sentence-3"
    program := opProgram
    query := .call "fmap" [fn, { ty := .const (.spec' "box" [int]), lvalue := true }] (.selected 0)
    source := "computed by resolve"
    prelude := prelude }

/-- No instance: the lookup is the primary, which has no `fmap`, so the
call is not viable rather than ill-formed. -/
def opObjectMissingSoft : Case :=
  { name := "op_object_missing_soft"
    cite := cite "temp.deduct.general#5.sentence-7"
    program := opProgram
    query := .call "fmap" [fn, { ty := int }] .noMatch
    source := "computed by resolve"
    prelude := prelude }

/-- Two instances match and neither is more specialized: substituting the
default instantiates an ambiguous lookup, and matching partial
specializations is part of instantiation, outside the immediate context,
so the call is ill-formed, not merely not viable. A worse fallback
candidate, a template so that no perfect-match shortcut applies, tells
the two apart: a compiler that treats the ambiguity as a deduction
failure selects it. Both compilers do (docs/findings.md). -/
def opObjectAmbiguousHard : Case :=
  { name := "op_object_ambiguous_hard"
    cite := cite "temp.deduct.general#8.sentence-4"
    program := opProgram
      [ .instance "functor" [typeParam] (.spec' "pair" [T, int])
      , .instance "functor" [typeParam] (.spec' "pair" [int, T]) ]
      [ .functionTemplate
          { name := "fmap", head := [typeParam]
            params := [.rref T, .lref (.const (.spec' "pair" [int, int]))] } ]
    query := .call "fmap" [fn, { ty := .spec' "pair" [int, int] }]
      (.illFormed "ambiguous partial specializations of functor<pair<int, int>>")
    source := "computed by resolve"
    prelude := prelude }

/-! ### The operation object as declared

`struct fmap_fn { template <...> operator()(...) const; }; inline constexpr
fmap_fn fmap{};`: the same `operator()` as `opObject`, found through the
object. A user's `fmap` beside the user's class is never a candidate. -/

private def user : Scope := [.namespace "user"]

private def objectProgram (extra : Program := []) : Program :=
  [ .class "Fn", .classTemplate "box" [typeParam], .classTemplate "pair" [typeParam, typeParam]
  , .lookup "functor", .instance "functor" [typeParam] (.spec' "box" [T]) ] ++
  opClass "functor" ++ extra

/-- The instance is found at the container's type, through the object. -/
def opClassSelects : Case :=
  { name := "op_class_selects"
    cite := cite "over.call.object#1.sentence-2"
    program := objectProgram
    query := .call "fmap" [fn, { ty := .spec' "box" [int] }] (.selected 0)
    source := "computed by resolve over the call operators"
    prelude := prelude }

/-- A user's `fmap(Fn, X)` beside the user's `X`, with an instance for
`X`: through the object, the user's function is never a candidate and
the operator is selected through the instance. -/
def opClassSuppressesAdl : Case :=
  { name := "op_class_suppresses_adl"
    cite := cite "basic.lookup.argdep#1"
    program := objectProgram
      [ .class "X" [] [] user, .instance "functor" [] (.named "X")
      , .function "fmap" [.named "Fn", .named "X"] user ]
    query := .call "fmap" [fn, { ty := .named "X" }] (.selected 0)
    source := "computed by resolve over the call operators"
    prelude := prelude }

/-- The same user declarations beside the operation as a free function
template: the user's function is found through the argument's namespace
and wins as a non-template exact match. -/
def opFreeAdmitsAdl : Case :=
  { name := "op_free_admits_adl"
    cite := cite "basic.lookup.argdep#1"
    program := opProgram [] [ .class "X" [] [] user, .instance "functor" [] (.named "X")
                            , .function "fmap" [.named "Fn", .named "X"] user ]
    query := .call "fmap" [fn, { ty := .named "X" }] (.selected 1)
    source := "computed by resolve"
    prelude := prelude }

/-- The audit's hidden member: the instance type's unconstrained `fmap`
hides the derivation base's constrained one, so a probe through the
instance says yes where the base's constraint would say no. -/
def hiddenConstrainedMember : Case :=
  { name := "class_member_lookup_3_hidden_constrained_member"
    cite := cite "class.member.lookup#3.sentence-2"
    program := [.class "Fn", .concept "fmap_shape" "false"] ++ hidingInstanceProgram
    query := .memberCall "opt_impl" "fmap" [fn, { ty := int }] (.selected 0)
    source := "computed by resolve over the member lookup"
    atomics := [("fmap_shape", [int], false)] }

/-! ### Pinning

The pinning pattern of beman.transpose's examples, `pinTemplate`: a user
function template with its own reference parameter defaulted to the
lookup. The program has an instance for `box<T>`, two unordered instances
for `pair`, and an instance object outside lookup to pin. -/

private def pinProgram : Program :=
  [ .classTemplate "box" [typeParam], .classTemplate "pair" [typeParam, typeParam]
  , .lookup "functor", .instance "functor" [typeParam] (.spec' "box" [T])
  , .instance "functor" [typeParam] (.spec' "pair" [T, int])
  , .instance "functor" [typeParam] (.spec' "pair" [int, T])
  , .object "my_functor", .functionTemplate (pinTemplate "functor" "use") ]

/-- Unpinned, the default takes the canonical instance: the argument is
the reference to the lookup. -/
def pinCanonical : Case :=
  { name := "pin_canonical"
    cite := cite "temp.deduct.general#5.sentence-2"
    program := pinProgram
    query := .deduction "use" [{ ty := .spec' "box" [int] }]
      (some [(0, .spec' "box" [int]), (1, .ref (.lookup "functor" (.spec' "box" [int])))])
    source := "computed by deduceTemplate"
    prelude := prelude }

/-- Unpinned with no instance: the default binds the primary, and with
no constraint the call is viable. A missing instance is an error in the
body, not a deduction failure. -/
def pinMissingViable : Case :=
  { name := "pin_missing_viable"
    cite := cite "temp.deduct.general#5.sentence-2"
    program := pinProgram
    query := .deduction "use" [{ ty := int }]
      (some [(0, int), (1, .ref (.lookup "functor" int))])
    source := "computed by deduceTemplate"
    prelude := prelude }

/-- Pinned: the explicit argument is used and the default is never
substituted. -/
def pinExplicit : Case :=
  { name := "pin_explicit"
    cite := cite "temp.deduct.general#2.sentence-2"
    program := pinProgram
    query := .deduction "use" [{ ty := int }]
      (some [(0, int), (1, .ref (.named "my_functor"))])
      (explicit := [int, .ref (.named "my_functor")])
    source := "computed by deduceTemplate"
    prelude := prelude }

/-- Pinned at a type whose canonical lookup is ambiguous: the lookup is
never instantiated, so the call is well-formed. -/
def pinExplicitAmbiguous : Case :=
  { name := "pin_explicit_ambiguous"
    cite := cite "temp.deduct.general#2.sentence-2"
    program := pinProgram
    query := .deduction "use" [{ ty := .spec' "pair" [int, int] }]
      (some [(0, .spec' "pair" [int, int]), (1, .ref (.named "my_functor"))])
      (explicit := [.spec' "pair" [int, int], .ref (.named "my_functor")])
    source := "computed by deduceTemplate"
    prelude := prelude }

/-! ### The by-value route

`byValueObject`, `traverse`'s by-value `POLICY` reduced to `fmap`: the
instance is a trailing function argument whose type defaults to the type
of the lookup, constrained by its shape. -/

private def byValueProgram (after : Program := []) : Program :=
  [ .class "Fn", .classTemplate "box" [typeParam], .classTemplate "pair" [typeParam, typeParam]
  , .lookup "functor", .instance "functor" [typeParam] (.spec' "box" [T])
  , .instance "functor" [typeParam] (.spec' "pair" [T, int])
  , .instance "functor" [typeParam] (.spec' "pair" [int, T])
  , .functionTemplate (byValueObject "functor") ] ++ after

private def policy : CallArg := { ty := .named "pinned_instance", lvalue := true }

/-- Omitted, the policy is the canonical instance. -/
def byValueCanonical : Case :=
  { name := "by_value_canonical"
    cite := cite "temp.deduct.general#5.sentence-2"
    program := byValueProgram
    query := .call "fmap_with" [fn, { ty := .spec' "box" [int] }] (.selected 0)
    source := "computed by resolve"
    prelude := prelude }

/-- Omitted with no instance: the policy type is `std::false_type`, which
has no `fmap`, so the constraint fails and the call is not viable. The
soft failure rests on the shapeless-default obligation. -/
def byValueMissingSoft : Case :=
  { name := "by_value_missing_soft"
    cite := cite "temp.deduct.general#5.sentence-7"
    program := byValueProgram
    query := .call "fmap_with" [fn, { ty := int }] .noMatch
    source := "computed by resolve"
    prelude := prelude }

/-- Passed: the policy is deduced from the argument and the default is
never substituted. -/
def byValueExplicit : Case :=
  { name := "by_value_explicit"
    cite := cite "temp.deduct.general#5.sentence-2"
    program := byValueProgram
    query := .call "fmap_with" [fn, { ty := int }, policy] (.selected 0)
    source := "computed by resolve"
    prelude := prelude }

/-- Passed at a type whose canonical lookup is ambiguous: the lookup is
never instantiated, so the call is well-formed. -/
def byValueExplicitAmbiguous : Case :=
  { name := "by_value_explicit_ambiguous"
    cite := cite "temp.deduct.general#5.sentence-2"
    program := byValueProgram
    query := .call "fmap_with" [fn, { ty := .spec' "pair" [int, int] }, policy] (.selected 0)
    source := "computed by resolve"
    prelude := prelude }

/-- Omitted at a type whose canonical lookup is ambiguous: substituting
the default instantiates the lookup, outside the immediate context, so
the call is ill-formed. A worse fallback tells soft from hard, as in
`op_object_ambiguous_hard`. -/
def byValueAmbiguousHard : Case :=
  { name := "by_value_ambiguous_hard"
    cite := cite "temp.deduct.general#8.sentence-4"
    program := byValueProgram
      [ .functionTemplate
          { name := "fmap_with", head := [typeParam]
            params := [.rref T, .lref (.const (.spec' "pair" [int, int]))] } ]
    query := .call "fmap_with" [fn, { ty := .spec' "pair" [int, int] }]
      (.illFormed "ambiguous partial specializations of functor<pair<int, int>>")
    source := "computed by resolve"
    prelude := prelude }

/-! ### The plan's routes, as an alternative design

The canonical operation object and the plan's three explicit-instance
routes as one overload set named `fmap`: candidates 0 to 3 are the
canonical object, the value route, the type route and the argument
route. -/

private def routesProgram : Program :=
  [ .class "Fn", .classTemplate "box" [typeParam], .classTemplate "pair" [typeParam, typeParam]
  , .lookup "functor", .instance "functor" [typeParam] (.spec' "box" [T])
  , .instance "functor" [typeParam] (.spec' "pair" [T, int])
  , .instance "functor" [typeParam] (.spec' "pair" [int, T])
  , .functionTemplate opObject, .functionTemplate valueRoute, .functionTemplate typeRoute
  , .functionTemplate argumentRoute ]

private def pinnedValue : Ty := .value (.obj "pinned_instance" .nil)
private def pinnedType : Ty := .named "pinned_instance"
private def ambiguousKey : CallArg := { ty := .spec' "pair" [int, int] }

/-- No explicit instance: only the canonical overload is viable. The
template-parameter routes cannot deduce the instance, and the argument
route has too few arguments. -/
def routesCanonical : Case :=
  { name := "routes_canonical"
    cite := cite "temp.deduct.type#4.sentence-4"
    program := routesProgram
    query := .call "fmap" [fn, { ty := .spec' "box" [int] }] (.selected 0)
    source := "computed by resolve"
    prelude := prelude }

/-- An instance value as the explicit argument: the value route. The
other three fail at the explicit argument, which has the wrong kind for
their first parameter. -/
def routesValue : Case :=
  { name := "routes_value"
    cite := cite "temp.deduct.general#2.sentence-2"
    program := routesProgram
    query := .call "fmap" [fn, { ty := int }] (.selected 1) (explicit := [pinnedValue])
    source := "computed by resolve"
    prelude := prelude }

/-- An instance type as the explicit argument: the type route. The
canonical overload takes the type as its `F`, deduces `T` and looks up
the instance; at `int` there is none and its constraint fails. -/
def routesType : Case :=
  { name := "routes_type"
    cite := cite "temp.deduct.general#2.sentence-2"
    program := routesProgram
    query := .call "fmap" [fn, { ty := int }] (.selected 2) (explicit := [pinnedType])
    source := "computed by resolve"
    prelude := prelude }

/-- An instance as a third argument: the argument route. -/
def routesArgument : Case :=
  { name := "routes_argument"
    cite := cite "over.match.viable#2.sentence-1"
    program := routesProgram
    query := .call "fmap" [fn, { ty := int }, policy] (.selected 3)
    source := "computed by resolve"
    prelude := prelude }

/-- The value route with its instance parameter typed as the pinned
instance's class, and a derived instance value supplied: the argument is
sliced to its base subobject, the route is viable, and the
specialization is the one the base's own value names
(`value_route_slices`). GCC applies the rule before P2308R1 and rejects
the argument (`probes.md`). -/
private def routesSlicedProgram : Program :=
  [ .class "Fn", .classTemplate "box" [typeParam], .class "derived_instance" [.named "pinned_instance"]
  , .lookup "functor", .instance "functor" [typeParam] (.spec' "box" [T])
  , .functionTemplate opObject, .functionTemplate (valueRouteAt "pinned_instance") ]

def routesValueSliced : Case :=
  { name := "routes_value_sliced"
    cite := cite "temp.arg.nontype#3.sentence-1"
    program := routesSlicedProgram
    query := .call "fmap" [fn, { ty := int }] (.selected 1)
      (explicit := [.value (.obj' "derived_instance" [.obj' "pinned_instance" []])])
    source := "computed by resolve"
    prelude := prelude }

/-- The value route at a type whose canonical lookup is ambiguous: the
canonical overload fails at the explicit argument, before its default is
substituted, so the call is well-formed. -/
def routesValueAmbiguous : Case :=
  { name := "routes_value_ambiguous"
    cite := cite "temp.deduct.general#2.sentence-2"
    program := routesProgram
    query := .call "fmap" [fn, ambiguousKey] (.selected 1) (explicit := [pinnedValue])
    source := "computed by resolve"
    prelude := prelude }

/-- The argument route at that type: the canonical overload fails at the
call, on the extra argument, before its default is substituted. -/
def routesArgumentAmbiguous : Case :=
  { name := "routes_argument_ambiguous"
    cite := cite "temp.deduct.general#5.sentence-1"
    program := routesProgram
    query := .call "fmap" [fn, ambiguousKey, policy] (.selected 3)
    source := "computed by resolve"
    prelude := prelude }

/-- The type route at that type: the canonical overload accepts the
instance type as its `F`, deduces `T`, and substitutes its default,
which instantiates the ambiguous lookup. The call is ill-formed although
the caller supplied an instance. Placing the instance first does not
protect the type route from the canonical overload. -/
def routesTypeAmbiguousHard : Case :=
  { name := "routes_type_ambiguous_hard"
    cite := cite "temp.deduct.general#8.sentence-4"
    program := routesProgram
    query := .call "fmap" [fn, ambiguousKey]
      (.illFormed "ambiguous partial specializations of functor<pair<int, int>>")
      (explicit := [pinnedType])
    source := "computed by resolve"
    prelude := prelude }

/-- The argument route with a default, as the library's by-value route
has, beside the canonical overload: both are viable for a call without
the policy, neither is more specialized, and their template parameters
differ, so constraints are not compared and the call is ambiguous. -/
def routesArgumentDefaultAmbiguous : Case :=
  { name := "routes_argument_default_ambiguous"
    cite := cite "over.match.best.general#3.sentence-1"
    program :=
      [ .class "Fn", .classTemplate "box" [typeParam]
      , .lookup "functor", .instance "functor" [typeParam] (.spec' "box" [T])
      , .functionTemplate opObject, .functionTemplate { byValueObject "functor" with name := "fmap" } ]
    query := .call "fmap" [fn, { ty := .spec' "box" [int] }] (.ambiguous [0, 1])
    source := "computed by resolve"
    prelude := prelude }

/-- Inheritance leak 1, at the instance type the concrete overload names:
the conversions tie and the non-template wins. -/
def rankLeakExact : Case :=
  { name := "leak_rank_exact"
    cite := cite "over.match.best.general#2"
    program := rankLeak
    query := .call "use" [{ ty := .named "applicative_i", lvalue := true }] (.selected 1)
    source := "computed by resolve"
    prelude := prelude }

/-- At an instance type derived from it, the template's exact match beats
the derived-to-base conversion before the non-template preference is
consulted. -/
def rankLeakDerived : Case :=
  { name := "leak_rank_derived"
    cite := cite "over.match.best.general#2"
    program := rankLeak
    query := .call "use" [{ ty := .named "monad_i", lvalue := true }] (.selected 0)
    source := "computed by resolve"
    prelude := prelude }

/-! ### A conversion between instance types -/

/-- At the Monad instance type, which converts to the Applicative one,
the generic template's identity beats the user-defined sequence. -/
def conversionLeakGeneric : Case :=
  { name := "conversion_leak_generic"
    cite := cite "over.ics.rank#2"
    program := conversionLeak
    query := .call "use" [monadInstance] (.selected 0)
    source := "computed by resolve"
    prelude := prelude }

/-- At the Applicative instance type the overload naming it wins the tie. -/
def conversionLeakConcrete : Case :=
  { name := "conversion_leak_concrete"
    cite := cite "over.match.best.general#2"
    program := conversionLeak
    query := .call "use" [{ ty := .named "applicative_i", lvalue := true }] (.selected 1)
    source := "computed by resolve"
    prelude := prelude }

/-- Two overloads reached by two different conversions are ambiguous. -/
def conversionSitesAmbiguous : Case :=
  { name := "conversion_sites_ambiguous"
    cite := cite "over.ics.rank#3"
    program := conversionSites
    query := .call "use" [monadInstance] (.ambiguous [0, 1])
    source := "computed by resolve"
    prelude := prelude }

/-- An explicit conversion is no candidate for argument passing. -/
def conversionExplicitDead : Case :=
  { name := "conversion_explicit_dead"
    cite := cite "over.match.copy#1"
    program := conversionExplicit
    query := .call "use" [monadInstance] .noMatch
    source := "computed by resolve"
    prelude := prelude }

/-- The typed value route with a Monad instance value that converts to
the pinned instance's class: the candidate initializer goes through the
conversion function, and the route is viable with the class's one
value. -/
private def routesConvertedProgram : Program :=
  [ .class "Fn", .classTemplate "box" [typeParam], .class "monad_instance"
  , .converting (.named "monad_instance") (.function (.named "pinned_instance"))
  , .lookup "functor", .instance "functor" [typeParam] (.spec' "box" [T])
  , .functionTemplate opObject, .functionTemplate (valueRouteAt "pinned_instance") ]

def routesValueConverted : Case :=
  { name := "routes_value_converted"
    cite := cite "temp.arg.nontype#3"
    program := routesConvertedProgram
    query := .call "fmap" [fn, { ty := int }] (.selected 1)
      (explicit := [.value (.obj' "monad_instance" [])])
    source := "computed by resolve"
    prelude := prelude }

/-! ### Inheritance erasure -/

/-- A function naming the Functor instance type accepts an Applicative
instance type derived from it. -/
def erasureInherited : Case :=
  { name := "erasure_named_base_inherited"
    cite := cite "over.ics.ref#1"
    program := namedBase
    query := .call "use" [{ ty := .named "applicative_i", lvalue := true }] (.selected 0)
    source := "computed by resolve"
    prelude := prelude }

/-- With the derivation replaced by composition, it accepts nothing: the
use is not at exact type, and erasure changes the outcome. -/
def erasureComposed : Case :=
  { name := "erasure_named_base_composed"
    cite := cite "over.match.viable#4.sentence-1"
    program := namedBase.eraseBases ["applicative_i"]
    query := .call "use" [{ ty := .named "applicative_i", lvalue := true }] .noMatch
    source := "computed by resolve"
    prelude := prelude }

/-! ### Deduction from a derived class -/

/-- `const derive_functor<T>&` deduces `T` from a class derived from
`derive_functor<opt_impl>`. -/
def deduceFromDerived : Case :=
  { name := "temp_deduct_call_4_derived"
    cite := cite "temp.deduct.call#4"
    program := derivedShape
    query := .deduction "use" [{ ty := .named "opt_monad_map", lvalue := true }]
      (some [(0, .named "opt_impl")])
    source := "computed by deduceTemplate"
    prelude := prelude }

/-- Two bases of the form `derive_functor<T>`: more than one possible
deduced `A`, so deduction fails. -/
def deduceFromTwoBases : Case :=
  { name := "temp_deduct_call_5_two_bases"
    cite := cite "temp.deduct.call#5.sentence-2"
    program := derivedShape ++
      [ .class "list_impl"
      , .class "two_maps" [.spec' "derive_functor" [.named "opt_impl"], .spec' "derive_functor" [.named "list_impl"]] ]
    query := .deduction "use" [{ ty := .named "two_maps", lvalue := true }] none
    source := "computed by deduceTemplate"
    prelude := prelude }

/-- Leak 2: the Monad instance type matches the Functor-shaped
signature. -/
def leakDerivedInherited : Case :=
  { name := "leak_derived_deduction_inherited"
    cite := cite "temp.deduct.call#4"
    program := derivedShape
    query := .call "use" [{ ty := .named "opt_monad_map", lvalue := true }] (.selected 0)
    source := "computed by resolve"
    prelude := prelude }

/-- With the derivation replaced by composition, it does not. -/
def leakDerivedComposed : Case :=
  { name := "leak_derived_deduction_composed"
    cite := cite "temp.deduct.call#4"
    program := derivedShape.eraseBases ["opt_monad_map"]
    query := .call "use" [{ ty := .named "opt_monad_map", lvalue := true }] .noMatch
    source := "computed by resolve"
    prelude := prelude }


/-! ### Phase 12: value nature, the copying rule, refinement -/

/-- The Monad instance type is trivially copyable, empty and
standard-layout. -/
def instanceTriviallyCopyable : Case :=
  { name := "instance_trivially_copyable"
    cite := cite "class.prop#1"
    program := instanceShapes
    query := .trait .isTriviallyCopyable [.named "monad_i"]
      (instanceShapes.trait .isTriviallyCopyable [.named "monad_i"] == .ok true)
    source := "computed by Program.trait" }
def instanceEmpty : Case :=
  { name := "instance_empty"
    cite := cite "meta.unary.prop#5"
    program := instanceShapes
    query := .trait .isEmpty [.named "monad_i"] (instanceShapes.trait .isEmpty [.named "monad_i"] == .ok true)
    source := "computed by Program.trait" }
def instanceStandardLayout : Case :=
  { name := "instance_standard_layout"
    cite := cite "class.prop#2"
    program := instanceShapes
    query := .trait .isStandardLayout [.named "monad_i"]
      (instanceShapes.trait .isStandardLayout [.named "monad_i"] == .ok true)
    source := "computed by Program.trait" }

/-- An instance type holding a reference is not copy assignable. -/
def referenceInstanceNotAssignable : Case :=
  { name := "reference_instance_not_assignable"
    cite := cite "class.copy.assign#7"
    program := referenceInstance
    query := .trait .isCopyAssignable [.named "ref_i"]
      (referenceInstance.trait .isCopyAssignable [.named "ref_i"] == .ok true)
    source := "computed by Program.trait" }

/-- The copying algorithm, constrained: not viable at the callable. -/
def copyConstraintShields : Case :=
  { name := "copy_constraint_shields"
    cite := cite "temp.constr.atomic#3.sentence-1"
    program := copyingAlgorithm true
    query := .call "run" [callable] .noMatch
    source := "computed by Program.call" }

/-- The copying algorithm, with the copy as a Mandate: ill-formed. -/
def copyMandateIllFormed : Case :=
  { name := "copy_mandate_ill_formed"
    cite := cite "dcl.fct.def.delete#2"
    program := copyingAlgorithm false
    query := .call "run" [callable] (.illFormed "a Mandate of the selected function is not met")
    source := "computed by Program.call" }

/-- Refinement by normalization: the Monad overload is selected at a
Monad instance. -/
def refinementSelectsMonad : Case :=
  { name := "refinement_selects_monad"
    cite := cite "temp.constr.normal#1"
    program := [ .concept "functor_shape" "true", .concept "applicative_shape" "true"
               , .concept "monad_shape" "true" ] ++ refinementOverloads
    query := .call "use" [{ ty := .named "monad_i", lvalue := true }] (.selected 1)
    source := "computed by Program.call"
    atomics := monadShapes }

/-- The Monad-constrained algorithm selects at a Monad instance; the laws
it owes are comments in the C++, since no compiler can check them. -/
def monadAlgorithmSelects : Case :=
  { name := "monad_algorithm_selects"
    cite := cite "res.on.requirements#1"
    program := [ .concept "functor_shape" "true", .concept "applicative_shape" "true"
               , .concept "monad_shape" "true" ] ++ monadAlgorithm
    query := .call "run" [{ ty := .named "monad_i", lvalue := true }] (.selected 0)
    source := "computed by Program.call"
    atomics := monadShapes }

/-- Every case of the encoding. -/
def cases : List Case :=
  [ opObjectSelects, opObjectNormalizedKey, opObjectMissingSoft, opObjectAmbiguousHard
  , opClassSelects, opClassSuppressesAdl, opFreeAdmitsAdl, hiddenConstrainedMember
  , pinCanonical, pinMissingViable, pinExplicit, pinExplicitAmbiguous, byValueCanonical
  , byValueMissingSoft, byValueExplicit, byValueExplicitAmbiguous, byValueAmbiguousHard
  , routesCanonical, routesValue, routesType, routesArgument, routesValueSliced, routesValueAmbiguous
  , routesArgumentAmbiguous, routesTypeAmbiguousHard, routesArgumentDefaultAmbiguous
  , rankLeakExact, rankLeakDerived, erasureInherited, erasureComposed, deduceFromDerived
  , deduceFromTwoBases, leakDerivedInherited, leakDerivedComposed
  , conversionLeakGeneric, conversionLeakConcrete, conversionSitesAmbiguous, conversionExplicitDead
  , routesValueConverted
  , instanceTriviallyCopyable, instanceEmpty, instanceStandardLayout, referenceInstanceNotAssignable
  , copyConstraintShields, copyMandateIllFormed, refinementSelectsMonad, monadAlgorithmSelects ]

/-- What the model computes for the encoding's cases, in the encoding's
environment. -/
def computed (c : Case) : Option (Option (List (ParamIdx × Ty))) :=
  computedWith (fun p a => Env.full p a (memberAtomics p)) c

def computedCall (c : Case) : Option (Resolution Nat) :=
  computedCallWith (fun p a => Env.full p a (memberAtomics p)) c

end Overload.Typeclass.Emit
