-- OverloadTest/Concepts.lean                                         -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of the library's concepts as the fragment states them. -/

open Overload Overload.Concepts

private def cA : Ty := .named "A"
private def cM : Ty := .named "M"
private def flat : Program := libraryConcepts ++ [.class "A"]
private def moveOnly : Program :=
  libraryConcepts ++
  [ .class "M", .special cM { kind := .copyCtor, body := .deleted }
  , .special cM { kind := .moveCtor, body := .defaulted, constParam := false } ]
private def refs : Program := libraryConcepts ++ [.class "R", .member (.named "R") { name := "r", ty := .lref (.named "int") }]

/-- The residue atoms as the C++ would answer them for a well-behaved class. -/
private def table (t : Ty) : List (String × List Ty × Bool) :=
  [ ("static_castable", [t, t], true), ("static_castable", [.lref t, t], true)
  , ("static_castable", [.lref (.const t), t], true), ("static_castable", [.const t, t], true)
  , ("swappable_lvalues", [t], true), ("common_reference_with", [.lref t, t], true)
  , ("common_reference_with", [.lref t, .lref t], true), ("common_reference_with", [.lref t, .lref (.const t)], true)
  , ("common_reference_with", [.lref t, .const t], true), ("equality_operators", [t], false) ]

private def sat (p : Program) (t : Ty) (c : String) : Bool :=
  Constraint.satisfied (Env.full p (table t)).atomic [] (p.normalize (.conceptId c [t])) == .ok true

#guard sat flat cA "destructible"
#guard sat flat cA "default_initializable"
#guard sat flat cA "move_constructible"
#guard sat flat cA "copy_constructible"
#guard sat flat cA "movable"
#guard sat flat cA "copyable"
#guard sat flat cA "semiregular"
#guard !sat flat cA "regular"
#guard sat moveOnly cM "move_constructible"
#guard !sat moveOnly cM "copy_constructible"
#guard !sat moveOnly cM "movable"
#guard sat refs (.named "R") "copy_constructible"
#guard !sat refs (.named "R") "default_initializable"
#guard !sat refs (.named "R") "copyable"
#guard Constraint.satisfied (Env.full flat).atomic [] (flat.normalize (.conceptId "same_as" [cA, cA])) == .ok true
#guard Constraint.satisfied (Env.full flat).atomic [] (flat.normalize (.conceptId "same_as" [cA, .const cA])) == .ok false

-- Laws through the bodies.
#guard libraryConcepts.laws "destructible" == []
#guard libraryConcepts.laws "move_constructible" == [moveConstructibleEqual, convertibleToEqual, equalityPreserving, stable, nonModifying]
#guard (libraryConcepts.laws "regular").contains swapExchanges
#guard (libraryConcepts.laws "semiregular").contains equalityComparableEqual == false
#guard flat.trait .isNothrowDestructible [cA] == .ok true
