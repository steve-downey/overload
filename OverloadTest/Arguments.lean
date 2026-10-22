-- OverloadTest/Arguments.lean                                        -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of template-argument conversion: the integer types, the type
of a literal, narrowing, and the converted constant. -/

open Overload

-- The ranges.
#guard representable "signed char" 1000 == some false
#guard representable "signed char" 127 == some true
#guard representable "unsigned" (-1) == some false
#guard representable "bool" 2 == some false
#guard representable "float" 1 == none
#guard covers "int" "char" == some true
#guard covers "signed char" "int" == some false
#guard covers "unsigned" "int" == some false

-- The type of a literal: the first of int, long, long long that holds it.
#guard literalType 1000 == some "int"
#guard literalType 2147483647 == some "int"
#guard literalType 2147483648 == some "long"
#guard literalType (-2147483648) == some "long"
#guard literalType 9223372036854775807 == some "long"  -- long is 64 bits under LP64
#guard literalType (-9223372036854775808) == none
#guard (Val.int 7).sourceType == some (.named "int")
#guard (Val.bool true).sourceType == some (.named "bool")
#guard (Val.obj "X" .nil).sourceType == some (.named "X")
#guard (Val.param 0).sourceType == none

-- Placeholders, anywhere under const, pointer or reference.
#guard (Ty.named "auto").hasPlaceholder
#guard (Ty.lref (.const (.named "auto"))).hasPlaceholder
#guard (Ty.lref (.const (.spec' "auto" [.named "shape"]))).hasPlaceholder
#guard !(Ty.named "int").hasPlaceholder
#guard !(Ty.lref (.const (.named "X"))).hasPlaceholder

-- Narrowing, the draft's example first: 1000 to signed char narrows, 1 does not.
#guard narrowing "int" "signed char" 1000 == some true
#guard narrowing "int" "signed char" 1 == some false
#guard narrowing "int" "unsigned" (-1) == some true
#guard narrowing "int" "unsigned" 0 == some false
#guard narrowing "int" "bool" 2 == some true
#guard narrowing "int" "bool" 1 == some false
-- A promotion never narrows.
#guard narrowing "char" "int" (-5) == some false
#guard narrowing "bool" "int" 1 == some false
-- Not integer types.
#guard narrowing "int" "X" 1 == none
#guard narrowing "X" "int" 1 == none

-- The converted constant.
#guard convertedConstant "int" (.int 1) == .ok (.int 1)
#guard convertedConstant "signed char" (.int 1000) matches .soft _
#guard convertedConstant "signed char" (.int 1) == .ok (.int 1)
#guard convertedConstant "long" (.int 2147483648) == .ok (.int 2147483648)
#guard convertedConstant "unsigned" (.int (-1)) matches .soft _
#guard convertedConstant "bool" (.int 1) == .ok (.bool true)
#guard convertedConstant "bool" (.int 0) == .ok (.bool false)
#guard convertedConstant "bool" (.int 2) matches .soft _
#guard convertedConstant "bool" (.bool false) == .ok (.bool false)
#guard convertedConstant "int" (.bool true) == .ok (.int 1)
#guard convertedConstant "int" (.obj "X" .nil) matches .soft _
#guard convertedConstant "X" (.int 1) matches .soft _
#guard convertedConstant "long long" (.int (-9223372036854775808)) matches .soft _

-- The base subobject of a class value. `struct B {}; struct D : B {}; struct E : D {};
-- struct X : D, B {};` (two B subobjects, through D and directly).
private def hier : Program :=
  [ .class "B", .class "D" [.named "B"], .class "E" [.named "D"], .class "X" [.named "D", .named "B"] ]
private def bVal : Val := .obj' "B" []
private def dVal : Val := .obj' "D" [bVal]
private def eVal : Val := .obj' "E" [dVal]
private def xVal : Val := .obj' "X" [dVal, bVal]
#guard hier.subobject (.named "B") dVal == some bVal
#guard hier.subobject (.named "B") eVal == some bVal
#guard hier.subobject (.named "D") eVal == some dVal
#guard hier.subobject (.named "B") bVal == some bVal
#guard hier.subobject (.named "B") xVal == none
#guard hier.subobject (.named "D") xVal == some dVal
#guard hier.subobject (.named "E") dVal == none
-- A value that does not spell its base subobject has none to slice.
#guard hier.subobject (.named "B") (.obj' "D" []) == none

-- The conversion against a parameter of each kind.
private def sub := hier.subobject
private def int : Ty := .named "int"
#guard convertArg sub [] .type int == .ok int
#guard convertArg sub [] .type (.value (.int 1)) matches .soft _
#guard convertArg sub [] (.const int) int matches .soft _
#guard convertArg sub [] (.const int) (.value (.int 1)) == .ok (.value (.int 1))
#guard convertArg sub [] (.const (.named "signed char")) (.value (.int 1000)) matches .soft _
#guard convertArg sub [] (.const (.named "bool")) (.value (.int 1)) == .ok (.value (.bool true))
-- Placeholders take the argument's own type.
#guard convertArg sub [] (.const (.named "auto")) (.value (.int 1000)) == .ok (.value (.int 1000))
#guard convertArg sub [] (.const (.lref (.const (.named "auto")))) (.ref (.named "o")) == .ok (.ref (.named "o"))
#guard convertArg sub [] (.const (.lref (.const (.spec' "auto" [.named "C"])))) (.value dVal) == .ok (.value dVal)
-- A dependent declared type waits; bound, it converts.
#guard convertArg sub [] (.const (.param 0)) (.value (.int 1000)) == .ok (.value (.int 1000))
#guard convertArg sub [(0, .named "signed char")] (.const (.param 0)) (.value (.int 1000)) matches .soft _
#guard convertArg sub [(0, int)] (.const (.param 0)) (.value (.int 1000)) == .ok (.value (.int 1000))
-- Top-level const is ignored.
#guard convertArg sub [] (.const (.const int)) (.value (.int 1)) == .ok (.value (.int 1))
-- Class values: the same class, a derived class sliced, an unrelated class, an ambiguous base.
#guard convertArg sub [] (.const (.named "B")) (.value bVal) == .ok (.value bVal)
#guard convertArg sub [] (.const (.named "B")) (.value dVal) == .ok (.value bVal)
#guard convertArg sub [] (.const (.named "B")) (.value eVal) == .ok (.value bVal)
#guard convertArg sub [] (.const (.named "D")) (.value bVal) matches .soft _
#guard convertArg sub [] (.const (.named "B")) (.value xVal) matches .soft _
#guard convertArg sub [] (.const (.named "B")) (.value (.int 1)) matches .soft _
#guard convertArg sub [] (.const int) (.value bVal) matches .soft _
-- References bind an object and refuse a temporary.
#guard convertArg sub [] (.const (.lref (.const (.named "B")))) (.ref (.named "o")) == .ok (.ref (.named "o"))
#guard convertArg sub [] (.const (.lref (.const (.named "B")))) (.value bVal) matches .soft _
-- Through the program's environment.
#guard convertArg (Env.ofProgram hier).subobject [] (.const (.named "B")) (.value dVal) == .ok (.value bVal)
