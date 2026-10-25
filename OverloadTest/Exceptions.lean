-- OverloadTest/Exceptions.lean                                       -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of exception specifications: the implicit ones of the special
members, the `is_nothrow_` traits, the function type's, and the
override check. -/

open Overload

private def cM : Ty := .named "M"
private def cX : Ty := .named "X"
private def cS : Ty := .named "S"
private def int : Ty := .named "int"

/-- `struct M { ~M() noexcept(false) {} }; struct X { M m; }; struct Y { M m; ~Y() noexcept {} };` -/
private def dtors : Program :=
  [ .class "M", .special cM { kind := .dtor, noexcept := some false }
  , .class "X", .member cX { name := "m", ty := cM }
  , .class "Y", .member (.named "Y") { name := "m", ty := cM }, .special (.named "Y") { kind := .dtor, noexcept := some true } ]

#guard dtors.throwing cM .dtor
#guard dtors.throwing cX .dtor
#guard !dtors.throwing (.named "Y") .dtor
#guard !dtors.throwing cX .copyCtor
#guard dtors.trait .isNothrowDestructible [cM] == .ok false
#guard dtors.trait .isNothrowDestructible [cX] == .ok false
#guard dtors.trait .isNothrowDestructible [.named "Y"] == .ok true
#guard dtors.trait .isNothrowDestructible [.lref cM] == .ok true
#guard dtors.trait .isDestructible [cM] == .ok true
#guard dtors.trait .isNothrowDestructible [int] == .ok true

/-- `struct M { M() {} M(const M&) {} M& operator=(const M&) { return *this; } }; struct X { M m; };` -/
private def userProvided : Program :=
  [ .class "M", .special cM { kind := .defaultCtor }, .special cM { kind := .copyCtor }
  , .special cM { kind := .copyAssign }
  , .class "X", .member cX { name := "m", ty := cM } ]

#guard userProvided.throwing cM .defaultCtor
#guard userProvided.throwing cX .defaultCtor
#guard userProvided.throwing cX .copyCtor
#guard userProvided.throwing cX .moveCtor
#guard userProvided.throwing cX .copyAssign
#guard !userProvided.throwing cM .dtor
#guard userProvided.trait .isNothrowDefaultConstructible [cX] == .ok false
#guard userProvided.trait .isDefaultConstructible [cX] == .ok true
#guard userProvided.trait .isNothrowCopyConstructible [cX] == .ok false
#guard userProvided.trait .isNothrowMoveConstructible [cX] == .ok false
#guard userProvided.trait .isNothrowCopyAssignable [cX] == .ok false
#guard userProvided.trait .isNothrowSwappable [cX] == .ok false
#guard userProvided.trait .isNothrowConvertible [cX, cX] == .ok false
#guard userProvided.trait .isNothrowConvertible [cX, .lref (.const cX)] == .ok true

/-- `struct X { int x; int y = may_throw<int>(); };` and a flat class. -/
private def flat : Program := [.class "X", .member cX { name := "x", ty := int }]
private def throwingInit : Program :=
  flat ++ [.member cX { name := "y", ty := int, init := true, throwingInit := true }]

#guard [SmfKind.defaultCtor, .copyCtor, .moveCtor, .copyAssign, .moveAssign, .dtor].all fun k => !flat.throwing cX k
#guard flat.trait .isNothrowDefaultConstructible [cX] == .ok true
#guard flat.trait .isNothrowCopyConstructible [cX] == .ok true
#guard flat.trait .isNothrowMoveAssignable [cX] == .ok true
#guard flat.trait .isNothrowSwappable [cX] == .ok true
#guard flat.trait .isNothrowSwappable [.const cX] == .ok false
#guard flat.trait .isNothrowConvertible [cX, cX] == .ok true
#guard throwingInit.throwing cX .defaultCtor
#guard !throwingInit.throwing cX .copyCtor
#guard throwingInit.trait .isNothrowDefaultConstructible [cX] == .ok false

-- Conversions and their specifiers.
private def convs : Program :=
  [ .class "S", .converting cS (.function int false true (some true))
  , .class "X", .converting cX (.constructor cS)
  , .class "Z", .converting (.named "Z") (.constructor cS false (some true)) ]
#guard convs.trait .isNothrowConvertible [cS, int] == .ok true
#guard convs.trait .isNothrowConstructible [cX, cS] == .ok false
#guard convs.trait .isConstructible [cX, cS] == .ok true
#guard convs.trait .isNothrowConstructible [.named "Z", cS] == .ok true
#guard convs.trait .isNothrowConvertible [cS, .named "Z"] == .ok true
#guard convs.trait .isNothrowConvertible [cS, cX] == .ok false

-- Function types carry their exception specification.
#guard flat.trait .isNothrowInvocable [Ty.fn' [int] int true, int] == .ok true
#guard flat.trait .isNothrowInvocable [Ty.fn' [int] int, int] == .ok false
#guard flat.trait .isInvocable [Ty.fn' [int] int, int] == .ok true
#guard userProvided.trait .isNothrowInvocable [Ty.fn' [cM] int true, .lref cM] == .ok false
#guard userProvided.trait .isNothrowInvocable [Ty.fn' [.lref (.const cM)] int true, .lref cM] == .ok true
#guard deduceTy (Ty.fn' [.param 0] int true) (Ty.fn' [int] int true) [] == some [(0, int)]
#guard deduceTy (Ty.fn' [.param 0] int) (Ty.fn' [int] int true) [] == none
#guard Ty.fn' [int] int true != Ty.fn' [int] int

-- A user swap is residue.
private def withSwap : Program := flat ++ [Decl.function "swap" [.lref cX, .lref cX]]
#guard (withSwap.trait .isNothrowSwappable [cX]).isOk == false

-- Overriding a non-throwing virtual function.
#guard !(overrideNoexceptProgram false).virtualsWellFormed
#guard (overrideNoexceptProgram true).virtualsWellFormed
