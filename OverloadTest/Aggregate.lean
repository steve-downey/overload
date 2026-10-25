-- OverloadTest/Aggregate.lean                                        -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of aggregates: which classes are, their elements, brace and
parenthesized aggregate initialization, implicit-lifetime classes, the
class value as the element list, and `T{}` as a requirement. -/

open Overload

private def cB : Ty := .named "B"
private def cD : Ty := .named "D"
private def cX : Ty := .named "X"
private def cM : Ty := .named "M"
private def int : Ty := .named "int"

/-- `struct B { int b; }; struct D : B { int& r; const int c; };` -/
private def agg : Program :=
  [ .class "B", .member cB { name := "b", ty := int }
  , .class "D" [cB], .member cD { name := "r", ty := .lref int }, .member cD { name := "c", ty := .const int } ]

#guard agg.aggregate cB && agg.aggregate cD
#guard !agg.aggregate int
#guard agg.elements cD == [cB, .lref int, .const int]
#guard agg.elementsWith cD == [(cB, false), (.lref int, false), (.const int, false)]
#guard agg.braceInit cB []
#guard agg.braceInit cB [{ ty := int }]
#guard !agg.braceInit cB [{ ty := int }, { ty := int }]
#guard !agg.braceInit cD []
#guard agg.braceInit cD [{ ty := cB }, { ty := int, lvalue := true }]
#guard agg.braceInit cD [{ ty := cB }, { ty := int, lvalue := true }, { ty := int }]
#guard !agg.braceInit cD [{ ty := cB }, { ty := int }]
#guard agg.trait .isConstructible [cD, cB, .lref int] == .ok true
#guard agg.trait .isConstructible [cD, cB, .lref int, int] == .ok true
#guard agg.trait .isConstructible [cD] == .ok false
#guard agg.trait .isConstructible [cB, int] == .ok true
#guard agg.trait .isConstructible [cB, cB] == .ok true
#guard agg.trait .isDefaultConstructible [cB] == .ok true
#guard agg.trait .isAggregate [cD] == .ok true
#guard agg.trait .isAggregate [.lref cD] == .ok false
#guard agg.trait .isImplicitLifetime [cD] == .ok true
#guard agg.trait .isImplicitLifetime [int] == .ok true
#guard agg.trait .isImplicitLifetime [.lref int] == .ok false
#guard agg.uniqueValue cB == none
#guard agg.uniqueValue cD == none

-- `struct X { const int c; };`: `X{}` but not `X x;`.
#guard constMemberProgram.braceInit cX []
#guard constMemberProgram.trait .isDefaultConstructible [cX] == .ok false
#guard constMemberProgram.requirementHolds (Env.full constMemberProgram) (.braceInit cX []) == .ok true
#guard (constMemberProgram.requirementHolds (Env.full constMemberProgram) (.braceInit (.param 0) [])).isOk == false
#guard constMemberProgram.requirementHolds (Env.full constMemberProgram) (.braceInit int []) == .ok true
#guard constMemberProgram.requirementHolds (Env.full constMemberProgram) (.braceInit (.lref int) []) == .ok false

/-- A member with a default member initializer stands in for the missing
initializer; a non-aggregate `T{}` is value-initialization. -/
private def withInit : Program :=
  [ .class "X", .member cX { name := "r", ty := .lref int, init := true }
  , .class "M", .special cM { kind := .defaultCtor }
  , .class "N", .member (.named "N") { name := "m", ty := cM }
  , .class "P", .converting (.named "P") (.constructor int) ]
#guard withInit.braceInit cX []
#guard !withInit.aggregate cM
#guard withInit.braceInit cM []
#guard withInit.braceInit (.named "N") []
#guard !withInit.braceInit (.named "P") []
#guard withInit.braceInit (.named "P") [{ ty := int }]
#guard withInit.trait .isConstructible [.named "P", int] == .ok true

-- Not aggregates: a user-declared constructor, a protected base, a virtual function.
#guard !Program.aggregate [.class "X", .special cX { kind := .defaultCtor, body := .defaulted }] cX
#guard !Program.aggregate [.class "B", .class "D" [] [cB]] cD
#guard !Program.aggregate [.class "B", .function "f" [] [.class "B"] .virtual] cB
#guard Program.aggregate [.class "B", .class "D" [cB]] cD

-- Implicit-lifetime classes beyond aggregates.
#guard !Program.implicitLifetimeClass [.class "X", .special cX { kind := .dtor }] cX
#guard Program.implicitLifetimeClass [.class "X", .special cX { kind := .defaultCtor }] cX
#guard !Program.implicitLifetimeClass [.class "X", .special cX { kind := .copyCtor }, .special cX { kind := .dtor }] cX

-- The class value is the element list, with one value only for classes of classes.
private def nested : Program := [.class "E", .class "F", .member (.named "F") { name := "e", ty := .named "E" }, .class "G" [.named "E"], .member (.named "G") { name := "f", ty := .named "F" }]
#guard nested.uniqueValue (.named "E") == some (.obj' "E" [])
#guard nested.uniqueValue (.named "F") == some (.obj' "F" [.obj' "E" []])
#guard nested.uniqueValue (.named "G") == some (.obj' "G" [.obj' "E" [], .obj' "F" [.obj' "E" []]])
#guard nested.elements (.named "G") == [.named "E", .named "F"]
