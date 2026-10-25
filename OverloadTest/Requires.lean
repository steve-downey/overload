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

/-! ## Compound and nested requirements -/

/-- `int g(A); A& h(A&); B k(A) noexcept; struct A { int get() const; };`
with the concepts `same_as`, `HasG = requires { g(declval<T>()); }` and
`Wraps = requires { requires HasG<T>; }`. -/
private def typed : Program :=
  [ .class "A", .class "B"
  , .function "g" [cA] [] .none none (.named "int")
  , .function "h" [.lref cA] [] .none none (.lref cA)
  , .function "k" [cA] [] .none (some true) cB
  , .function "get" [] [.class "A"] .none none (.named "int")
  , .conceptDef "same_as" 2 (.trait .isSame [.param 0, .param 1])
  , .conceptDef "HasG" 1 (.requires [.simple "g" [.param 0]] [.param 0])
  , .conceptDef "Wraps" 1 (.requires [.nested (.conceptId "HasG" [.param 0])] [.param 0]) ]
private def tenv : Env := Env.full typed
private def tbase : Env := Env.ofProgram typed

-- What an expression is: its type is the selected function's return
-- type, a reference included, and it throws unless the function says not.
#guard typed.expression tbase (.simple "g" [cA]) == .ok (some { ty := .named "int", throwing := some true })
#guard typed.expression tbase (.simple "h" [.lref cA]) == .ok (some { ty := .lref cA, throwing := some true })
#guard typed.expression tbase (.simple "k" [cA]) == .ok (some { ty := cB, throwing := some false })
#guard typed.expression tbase (.simple "g" [cB]) == .ok none
#guard typed.expression tbase (.memberCall cA "get" []) == .ok (some { ty := .named "int", throwing := some true })
#guard typed.expression tbase (.braceInit cA []) == .ok (some { ty := cA })
#guard typed.expression tbase (.type cA) == .soft "the requirement is not an expression"

-- Compound requirements: the return-type-requirement on `decltype((E))`.
#guard typed.requirementHolds tbase (.compound (.simple "g" [cA]) (some ("same_as", [.named "int"]))) == .ok true
#guard typed.requirementHolds tbase (.compound (.simple "g" [cA]) (some ("same_as", [cA]))) == .ok false
#guard typed.requirementHolds tbase (.compound (.simple "h" [.lref cA]) (some ("same_as", [.lref cA]))) == .ok true
#guard typed.requirementHolds tbase (.compound (.simple "h" [.lref cA]) (some ("same_as", [cA]))) == .ok false
#guard typed.requirementHolds tbase (.compound (.simple "g" [cB]) (some ("same_as", [.named "int"]))) == .ok false
#guard typed.requirementHolds tbase (.compound (.simple "g" [cA])) == .ok true
#guard typed.requirementHolds tbase (.compound (.simple "g" [cB])) == .ok false
#guard typed.requirementHolds tbase (.compound (.memberCall cA "get" []) (some ("same_as", [.named "int"]))) == .ok true
#guard typed.requirementHolds tbase (.compound (.braceInit cA []) (some ("same_as", [cA]))) == .ok true
#guard typed.requirementHolds tbase (.compound (.type cA) (some ("same_as", [cA]))) == .ok false

-- The noexcept-specifier.
#guard typed.requirementHolds tbase (.compound (.simple "k" [cA]) none true) == .ok true
#guard typed.requirementHolds tbase (.compound (.simple "g" [cA]) none true) == .ok false
#guard typed.requirementHolds tbase (.compound (.simple "k" [cA]) (some ("same_as", [cB])) true) == .ok true
#guard typed.requirementHolds tbase (.compound (.simple "k" [cA]) (some ("same_as", [cA])) true) == .ok false
-- Whether a braced initialization throws is outside the fragment: soft,
-- so the requires-expression is `false`.
#guard typed.requirementHolds tbase (.compound (.braceInit cA []) none true)
  == .soft "whether the expression throws is outside the fragment"
#guard typed.requirementsHold tbase [.compound (.braceInit cA []) none true] == .ok false

-- Nested requirements: satisfied in the environment, concept-ids expanded.
#guard typed.requirementHolds tbase (.nested (.conceptId "same_as" [cA, cA])) == .ok true
#guard typed.requirementHolds tbase (.nested (.conceptId "same_as" [cA, cB])) == .ok false
#guard typed.requirementHolds tbase (.nested (.trait .isClass [cA])) == .ok true
#guard typed.requirementHolds tbase (.nested (.conj (.trait .isClass [cA]) (.trait .isClass [.named "int"]))) == .ok false
#guard typed.requirementHolds tbase (.nested (.disj (.trait .isClass [cA]) (.trait .isClass [.named "int"]))) == .ok true
#guard typed.requirementHolds tbase (.nested (.conceptId "Nope" [cA])) == .hard "the concept Nope is not declared"

-- A nested concept whose body is a requires-expression: the base
-- environment answers it softly, the full one to the program's depth.
#guard typed.requirementHolds tbase (.nested (.conceptId "HasG" [cA])) == .ok false
#guard typed.requirementHolds tenv (.nested (.conceptId "HasG" [cA])) == .ok true
#guard typed.requirementHolds tenv (.nested (.conceptId "HasG" [cB])) == .ok false
#guard Constraint.satisfied tenv.atomic [(0, cA)] (typed.normalize (.conceptId "Wraps" [.param 0])) == .ok true
#guard Constraint.satisfied tenv.atomic [(0, cB)] (typed.normalize (.conceptId "Wraps" [.param 0])) == .ok false
#guard Constraint.satisfied (Env.fullWithin typed [] (fun e _ => .soft e) typed.trait 1).atomic [(0, cA)]
  (typed.normalize (.conceptId "Wraps" [.param 0])) == .ok false

-- The equivalence of the compound form with the simple and nested ones,
-- on the program.
#guard typed.requirementsHold tbase [.compound (.simple "g" [cA]) (some ("same_as", [.named "int"]))] ==
  typed.requirementsHold tbase [.simple "g" [cA], .nested (.conceptId "same_as" [.named "int", .named "int"])]
#guard typed.requirementsHold tbase [.compound (.simple "g" [cB]) (some ("same_as", [.named "int"]))] ==
  typed.requirementsHold tbase [.simple "g" [cB]]

-- Substitution reaches the new forms.
#guard (Constraint.Requirement.compound (.simple "g" [.param 0]) (some ("same_as", [.param 1]))).subst [(0, cA), (1, cB)]
  == .compound (.simple "g" [cA]) (some ("same_as", [cB]))
#guard (Constraint.Requirement.nested (.conj (.conceptId "C" [.param 0]) (.trait .isClass [.param 0]))).subst [(0, cA)]
  == .nested (.conj (.conceptId "C" [cA]) (.trait .isClass [cA]))
