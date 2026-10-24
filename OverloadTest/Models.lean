-- OverloadTest/Models.lean                                           -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of semantic requirements, modelling and the verdict. -/

open Overload

private def lawA : Semantic := { slug := "law-a", statement := "a" }
private def lawB : Semantic := { slug := "law-b", statement := "b" }
private def cT : Ty := .named "T"

/-- `concept Base = is_class<T>; concept Refined = Base<T> && is_empty<T>;`,
each with a law, and a template constrained by `Refined`. -/
private def refined : Program :=
  [ .class "T"
  , .conceptDef "Base" 1 (.trait .isClass [.param 0]), .semantic "Base" lawA
  , .conceptDef "Refined" 1 (.conj (.conceptId "Base" [.param 0]) (.trait .isEmpty [.param 0]))
  , .semantic "Refined" lawB
  , .functionTemplate { name := "f", head := [{ kind := .type }], params := [.param 0]
                        constraint := some (.conceptId "Refined" [.param 0]) } ]
private def env : Env := Env.full refined

-- The laws of a concept include those of the concepts its body names.
#guard refined.lawsOf "Refined" == [lawB]
#guard refined.laws "Refined" == [lawB, lawA]
#guard refined.laws "Base" == [lawA]
#guard refined.laws "Nope" == []

-- The uses a call depends on, and the verdicts.
#guard (refined.call env (refined.candidates "f") [{ ty := cT }]).map (·.index) == .selected 0
#guard refined.modelVerdicts env [] (refined.candidates "f") [{ ty := cT }] ==
  [.satisfiedNotModeled "Refined" [cT] lawB, .satisfiedNotModeled "Refined" [cT] lawA]
#guard refined.modelVerdicts env [(lawB, [cT])] (refined.candidates "f") [{ ty := cT }] ==
  [.satisfiedNotModeled "Refined" [cT] lawA]
#guard refined.modelVerdicts env [(lawA, [cT]), (lawB, [cT])] (refined.candidates "f") [{ ty := cT }] == []
-- A claim for other arguments does not count.
#guard refined.modelVerdicts env [(lawA, [.named "int"]), (lawB, [cT])] (refined.candidates "f") [{ ty := cT }] ==
  [.satisfiedNotModeled "Refined" [cT] lawA]
-- No selection, no verdict.
#guard refined.modelVerdicts env [] (refined.candidates "f") [{ ty := .named "int" }] == []

-- A disjunction: a concept-id the arguments do not satisfy gives no verdict.
private def either : Program :=
  [ .class "T"
  , .conceptDef "Scalar" 1 (.trait .isScalar [.param 0]), .semantic "Scalar" lawA
  , .conceptDef "Class" 1 (.trait .isClass [.param 0]), .semantic "Class" lawB
  , .functionTemplate { name := "f", head := [{ kind := .type }], params := [.param 0]
                        constraint := some (.disj (.conceptId "Scalar" [.param 0]) (.conceptId "Class" [.param 0])) } ]
#guard either.modelVerdicts (Env.full either) [] (either.candidates "f") [{ ty := cT }] ==
  [.satisfiedNotModeled "Class" [cT] lawB]
