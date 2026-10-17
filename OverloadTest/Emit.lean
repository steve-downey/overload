-- OverloadTest/Emit.lean                                             -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of the C++ emitter: every stated deduction expectation agrees
with what the model computes, and the rendering has the shape the
differential harness reads. -/

open Overload Overload.Emit

-- Every deduction case's stated expectation is what `deduceTemplate`
-- computes.
#guard cases.all fun c =>
  match c.query with
  | .deduction .. => stated c == computed c && (computed c).isSome
  | _ => true

-- Every call case's stated expectation is what `invoke` computes under
-- the text: resolution, then the selected function's Mandates.
#guard cases.all fun c =>
  match c.query, computedCall c with
  | .call _ _ expected _, some got => Resolution.agree expected got
  | .call .., none => false
  | _, _ => true

-- Every lookup case's stated expectation is what `select` computes.
#guard cases.all fun c =>
  match c.query, computedLookup c with
  | .lookup _ _ expected, some got => Resolution.agree expected got
  | .lookup .., none => false
  | _, _ => true

-- Names are unique, so the emitted files do not collide.
#guard (cases.map (·.name)).eraseDups.length == cases.length

-- The first line carries the expectation the harness reads.
#guard (render draftDeductCall3_rvalue).startsWith "// expect: well-formed\n"
#guard ((render draftDeductCall3_rvalue).splitOn
  "static_assert(std::is_same_v<decltype(f(std::declval<int>())), deduced<int>>);").length == 2
#guard ((render pointerMismatch).splitOn "static_assert(!viable<int>);").length == 2
#guard ((render forwardingLvalue).splitOn "std::declval<int&>()").length == 2
#guard ((render nonTemplatePreferred).splitOn "selected<1>").length == 3
#guard ((render draftDeductGeneral5_explicit).splitOn "decltype(f<int>())").length == 2
#guard ((render draftDeductGeneral5_default).splitOn "f(T0 = {}, T1 = {})").length == 2
#guard ((render stepOrderHazard).splitOn "const auto& T1 = functor<T0>").length == 2
#guard ((render stepOrderHazard).splitOn "using probe = decltype(f(").length == 2
#guard (render stepOrderHazard).startsWith "// expect: ill-formed\n"
#guard ((render stepOrderSoft).splitOn "requires (!std::is_same_v").length == 2
#guard ty (.spec' "C" [.named "int", .ptr (.param 0)]) == "C<int, T0*>"
#guard ty (.const (.lref (.param 0))) == "const T0&"
