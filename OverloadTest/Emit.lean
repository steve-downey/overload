-- OverloadTest/Emit.lean                                             -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of the C++ emitter: every stated deduction expectation agrees
with what the model computes, and the rendering has the shape the
differential harness reads. -/

open Overload Overload.Emit

-- Every deduction case's stated expectation is what `deduceCall` computes.
#guard cases.all fun c =>
  match c.query, computed c with
  | .deduction _ _ expected, some got => expected == got
  | .deduction .., none => false
  | .call .., _ => true

-- Names are unique, so the emitted files do not collide.
#guard (cases.map (·.name)).eraseDups.length == cases.length

-- The first line carries the expectation the harness reads.
#guard (render draftDeductCall3_rvalue).startsWith "// expect: well-formed\n"
#guard ((render draftDeductCall3_rvalue).splitOn
  "static_assert(std::is_same_v<decltype(f(std::declval<int>())), deduced<int>>);").length == 2
#guard ((render pointerMismatch).splitOn "static_assert(!viable<int>);").length == 2
#guard ((render forwardingLvalue).splitOn "std::declval<int&>()").length == 2
#guard ((render nonTemplatePreferred).splitOn "selected<1>").length == 3
#guard ty (.spec' "C" [.named "int", .ptr (.param 0)]) == "C<int, T0*>"
#guard ty (.const (.lref (.param 0))) == "const T0&"
