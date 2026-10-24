-- OverloadTest/Emit.lean                                             -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of the C++ emitter: every stated expectation agrees with what
the model computes, on both sides, and the rendering has the shape the
differential harness reads. -/

open Overload Overload.Emit

/-- Every deduction case's stated expectation is what `deduceTemplate`
computes, in the environment given. -/
private def deductionsAgree (computed : Case → Option (Option (List (ParamIdx × Ty)))) (cs : List Case) :
    Bool :=
  cs.all fun c =>
    match c.query with
    | .deduction .. => stated c == computed c && (computed c).isSome
    | _ => true

/-- Every call case's stated expectation is what `Program.call` computes
under the text: resolution, the access check, then the selected function's
Mandates. -/
private def callsAgree (computedCall : Case → Option (Resolution Nat)) (cs : List Case) : Bool :=
  cs.all fun c =>
    match c.query, computedCall c with
    | .call _ _ expected _ _, some got => Resolution.agree expected got
    | .call .., none => false
    | .memberCall _ _ _ expected _, some got => Resolution.agree expected got
    | .memberCall .., none => false
    | .dependentCall _ expected, some got => Resolution.agree expected got
    | .dependentCall .., none => false
    | _, _ => true

/-- Every lookup case's stated expectation is what `select` computes. -/
private def lookupsAgree (cs : List Case) : Bool :=
  cs.all fun c =>
    match c.query, computedLookup c with
    | .lookup _ _ expected, some got => Resolution.agree expected got
    | .lookup .., none => false
    | _, _ => true

/-- Every trait case's stated expectation is what `Trait.answer` computes. -/
private def traitsAgree (cs : List Case) : Bool :=
  cs.all fun c =>
    match c.query, computedTrait c with
    | .trait _ _ expected, some got => expected == got
    | .trait .., none => false
    | _, _ => true

-- The Standard side's cases, in the program's own environment.
#guard deductionsAgree computed cases
#guard traitsAgree cases
#guard callsAgree computedCall cases
#guard lookupsAgree cases

-- The encoding's cases, in the encoding's environment.
#guard deductionsAgree Typeclass.Emit.computed Typeclass.Emit.cases
#guard callsAgree Typeclass.Emit.computedCall Typeclass.Emit.cases
#guard lookupsAgree Typeclass.Emit.cases

-- Names are unique across both lists, so the emitted files do not collide.
#guard ((cases ++ Typeclass.Emit.cases).map (·.name)).eraseDups.length ==
  (cases ++ Typeclass.Emit.cases).length

-- The first line carries the expectation the harness reads.
#guard (render draftDeductCall3_rvalue).startsWith "// expect: well-formed\n"
#guard ((render draftDeductCall3_rvalue).splitOn
  "static_assert(std::is_same_v<decltype(f(std::declval<int>())), deduced<int>>);").length == 2
#guard ((render pointerMismatch).splitOn "static_assert(!viable<int>);").length == 2
#guard ((render forwardingLvalue).splitOn "std::declval<int&>()").length == 2
#guard ((render nonTemplatePreferred).splitOn "selected<1>").length == 3
#guard ((render draftDeductGeneral5_explicit).splitOn "decltype(f<int>())").length == 2
#guard ((render draftDeductGeneral5_default).splitOn "f(T0 = {}, T1 = {})").length == 2
#guard ((render stepOrderHazard).splitOn "const auto& T1 = trait<T0>").length == 2
#guard ((render stepOrderHazard).splitOn "using probe = decltype(f(").length == 2
#guard (render stepOrderHazard).startsWith "// expect: ill-formed\n"
#guard ((render stepOrderSoft).splitOn "requires (!std::is_same_v").length == 2
-- Converted constant arguments: the call with its explicit argument, the cast to the
-- parameter's type in the expectation, and the sliced class value.
#guard ((render draftDeductGeneral12_narrowing).splitOn "f<1000>(std::declval<int>())").length == 2
#guard ((render intToLong).splitOn "value_of<static_cast<long>(1)>").length == 2
#guard ((render derivedToBaseValue).splitOn "f<D{B{}}>()").length == 2
#guard ((render derivedToBaseValue).splitOn "value_of<B{}>").length == 2
#guard ((render derivedToBaseValue).splitOn "template <B T0>").length == 2
-- The encoding's cases carry their prelude: an instance has the operation,
-- and the operation object's constraint is the concept the prelude declares.
#guard ((render Typeclass.Emit.opObjectSelects).splitOn "static void fmap(F&&, X&&)").length == 3
#guard ((render Typeclass.Emit.opObjectSelects).splitOn "requires fmap_call<T2, T0, T1>").length == 2
#guard ((render stepOrderHazard).splitOn "fmap").length == 1
#guard ty (.spec' "C" [.named "int", .ptr (.param 0)]) == "C<int, T0*>"
#guard ty (.const (.lref (.param 0))) == "const T0&"
