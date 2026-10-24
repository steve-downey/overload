-- OverloadTest/Requires.lean                                         -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of concept normalization and requires-expressions. -/

open Overload

private def tparam : TemplateParam := { kind := .type }
private def cA : Ty := .named "A"
private def cB : Ty := .named "B"

/-- `concept C1 = is_class<T>; concept C2 = C1<T> && is_empty<T>;` -/
private def refined : Program :=
  [ .class "A", .conceptDef "C1" 1 (.trait .isClass [.param 0])
  , .conceptDef "C2" 1 (.conj (.conceptId "C1" [.param 0]) (.trait .isEmpty [.param 0])) ]

#guard refined.normalize (.conceptId "C2" [.param 3]) ==
  .conj (.trait .isClass [.param 3]) (.trait .isEmpty [.param 3])
#guard refined.normalize (.conceptId "C1" [cA]) == .trait .isClass [cA]
#guard refined.normalize (.conceptId "Nope" [cA]) == .conceptId "Nope" [cA]
#guard Constraint.subsumes (refined.normalize (.conceptId "C2" [.param 0]))
  (refined.normalize (.conceptId "C1" [.param 0]))
#guard !Constraint.subsumes (refined.normalize (.conceptId "C1" [.param 0]))
  (refined.normalize (.conceptId "C2" [.param 0]))
-- Compared by name, the concept-ids do not subsume one another.
#guard !Constraint.subsumes (.conceptId "C2" [.param 0]) (.conceptId "C1" [.param 0])

-- An unexpanded concept-id is a hard error in the program's environment.
#guard Constraint.satisfied (Env.full refined).atomic [(0, cA)] (.conceptId "Nope" [.param 0]) ==
  .hard "the concept Nope is not declared"
#guard Constraint.satisfied (Env.full refined).atomic [(0, cA)] (refined.normalize (.conceptId "C2" [.param 0])) ==
  .ok true

/-- `void g(A);` and a member `get` of `A`. -/
private def calls : Program :=
  [ .class "A", .class "B", .function "g" [cA], .function "get" [] [.class "A"], .classTemplate "S" [tparam] ]
private def env : Env := Env.full calls
private def base : Env := Env.ofProgram calls

#guard calls.requirementHolds base (.simple "g" [cA]) == .ok true
#guard calls.requirementHolds base (.simple "g" [cB]) == .ok false
#guard calls.requirementHolds base (.simple "h" [cA]) == .ok false
#guard calls.requirementHolds base (.memberCall cA "get" []) == .ok true
#guard calls.requirementHolds base (.memberCall cB "get" []) == .ok false
#guard calls.requirementHolds base (.type (Ty.spec' "S" [cA])) == .ok true
#guard calls.requirementHolds base (.type (Ty.spec' "S" [cA, cB])) == .ok false
#guard calls.requirementHolds base (.type (Ty.spec' "R" [cA])) == .ok false
#guard calls.requirementHolds base (.type cA) == .ok true
#guard calls.requirementHolds base (.type (.named "int")) == .ok true
#guard calls.requirementHolds base (.type (.named "Zed")) == .ok false

-- Lexical order: the first failing requirement decides, and the
-- expression is never soft.
#guard calls.requirementsHold base [.simple "g" [cA], .type (Ty.spec' "S" [cA])] == .ok true
#guard calls.requirementsHold base [.simple "g" [cB], .type (Ty.spec' "R" [cA])] == .ok false
#guard calls.requirementsHold base [] == .ok true

-- Through a constraint: the full environment answers, the base does not.
#guard Constraint.satisfied env.atomic [(0, cA)] (.requires [.simple "g" [.param 0]] [.param 0]) == .ok true
#guard Constraint.satisfied env.atomic [(0, cB)] (.requires [.simple "g" [.param 0]] [.param 0]) == .ok false
#guard Constraint.satisfied base.atomic [(0, cA)] (.requires [.simple "g" [.param 0]] [.param 0]) == .ok false
