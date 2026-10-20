-- OverloadTest/DependentCandidate.lean                               -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of dependent calls: the lookup in two contexts, and the verdict
of [temp.dep.candidate]/1. -/

open Overload

private def int : Ty := .named "int"
private def N : Scope := [.namespace "N"]
private def x : CallArg := { ty := .named "X", lvalue := true }

-- The instantiation context finds what the definition context could not.
#guard resGeneral1Program.dependentLookup 1 [] "f" [{ ty := .named "E" }] ==
  [.function "f" [.named "char"], .function "f" [.named "E"]]
#guard resGeneral1Program.dependentLookup 1 [] "f" [{ ty := .named "char" }] ==
  [.function "f" [.named "char"]]
#guard (resGeneral1Program.dependentCallAt (Env.ofProgram resGeneral1Program) 1 [] "f"
  [{ ty := .named "E" }]).map (·.index) == .selected 1
-- A fundamental type has no associated namespace, so nothing is found later.
#guard Program.dependentLookup [.dependentCall "f" [{ ty := int }], .function "f" [int]] 0 [] "f"
  [{ ty := int }] == []
#guard (Program.dependentCallAt [.dependentCall "f" [{ ty := int }], .function "f" [int]]
  (Env.ofProgram []) 0 [] "f" [{ ty := int }]) matches .illFormed _

-- The verdict: another unit's better overload.
#guard Units.dependentVerdicts [unitWithBaseOverload] == []
#guard Units.dependentVerdicts [unitWithBaseOverload, unitWithExactOverload] ==
  [.dependentCandidate 0 3 "f" [x]]
#guard Units.dependentVerdicts [unitWithExactOverload, unitWithBaseOverload] ==
  [.dependentCandidate 1 3 "f" [x]]
-- The same overload in both units: no verdict.
#guard Units.dependentVerdicts [unitWithBaseOverload, unitWithBaseOverload] == []
-- A unit whose other declares a worse match, not a better one: no verdict either.
#guard Units.dependentVerdicts
  [ [.class "B" [] [] N, .class "X" [.named "B"] [] N, .function "f" [.named "X"] N, .dependentCall "f" [x]]
  , [.class "B" [] [] N, .function "f" [.named "B"] N] ] == []
-- All verdicts together.
#guard Units.allVerdicts [unitWithBaseOverload, unitWithExactOverload] ==
  [.dependentCandidate 0 3 "f" [x]]

-- An object as the callee: argument-dependent lookup never applies, so no verdict.
private def objectUnit : Program :=
  [ .class "fn", .function "operator()" [.named "X"] [.class "fn"], .object "f" "fn"
  , .class "X" [] [] N, .dependentCall "f" [x] ]
private def otherUnit : Program := [ .class "X" [] [] N, .function "f" [.named "X"] N ]
#guard Units.dependentVerdicts [objectUnit, otherUnit] == []
#guard (objectUnit.dependentCallAt (Env.ofProgram objectUnit) 4 [] "f" [x]).map (·.index) == .selected 0
