-- OverloadTest/Traits.lean                                           -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of the traits the program answers. -/

open Overload

private def cB : Ty := .named "B"
private def cD : Ty := .named "D"
private def cX : Ty := .named "X"
private def cM : Ty := .named "M"
private def int : Ty := .named "int"
private def derivation : Program := [.class "B", .class "D" [cB]]

#guard derivation.trait .isBaseOf [cB, cD] == .ok true
#guard derivation.trait .isBaseOf [.const cB, cD] == .ok true
#guard derivation.trait .isBaseOf [cD, cB] == .ok false
#guard derivation.trait .isBaseOf [int, int] == .ok false
#guard derivation.trait .isBaseOf [cB, .param 0] == .soft "std::is_base_of_v of a dependent type"

#guard derivation.trait .isConvertible [cD, cB] == .ok true
#guard derivation.trait .isConvertible [cB, cD] == .ok false
#guard derivation.trait .isConvertible [cD, .lref (.const cB)] == .ok true
#guard derivation.trait .isConvertible [cD, .lref cB] == .ok false
#guard derivation.trait .isConvertible [.named "void", .named "void"] == .ok true
#guard derivation.trait .isConvertible [int, .named "void"] == .ok false
#guard derivation.trait .isConvertible [int, int] == .ok true
#guard (derivation.trait .isConvertible [int, .named "long"]).isOk == false

/-- `struct M { M(const M&) = delete; }; struct X { M m; };` -/
private def deletedMember : Program :=
  [ .class "M", .special cM { kind := .copyCtor, body := .deleted }
  , .class "X", .member cX { name := "m", ty := cM } ]
#guard deletedMember.trait .isCopyConstructible [cX] == .ok false
#guard deletedMember.trait .isMoveConstructible [cX] == .ok false
-- `M` has a user-declared constructor and so no default constructor, and
-- `X`'s defaulted default constructor is defined as deleted through it.
#guard deletedMember.trait .isDefaultConstructible [cM] == .ok false
#guard deletedMember.trait .isDefaultConstructible [cX] == .ok false
#guard deletedMember.trait .isConstructible [cX] == .ok false
#guard deletedMember.trait .isConstructible [cX, .lref (.const cX)] == .ok false
#guard deletedMember.trait .isConvertible [cX, cX] == .ok false
#guard deletedMember.trait .isCopyAssignable [cX] == .ok true
#guard deletedMember.trait .isTriviallyCopyable [cX] == .ok true
#guard deletedMember.trait .isDestructible [cX] == .ok true

/-- `struct X { int& r; };` -/
private def refMember : Program := [.class "X", .member cX { name := "r", ty := .lref int }]
#guard refMember.trait .isDefaultConstructible [cX] == .ok false
#guard refMember.trait .isCopyConstructible [cX] == .ok true
#guard refMember.trait .isCopyAssignable [cX] == .ok false
#guard refMember.trait .isMoveAssignable [cX] == .ok false
#guard refMember.trait .isTriviallyCopyable [cX] == .ok true
#guard refMember.trait .isStandardLayout [cX] == .ok false
#guard refMember.trait .isTriviallyCopyConstructible [cX] == .ok true

-- Scalars and references.
#guard derivation.trait .isAssignable [.lref int, int] == .ok true
#guard derivation.trait .isAssignable [int, int] == .ok false
#guard derivation.trait .isAssignable [.lref (.const int), int] == .ok false
#guard derivation.trait .isAssignable [.lref (.const cB), cB] == .ok false
#guard derivation.trait .isDestructible [.lref cB] == .ok true
#guard derivation.trait .isDestructible [.named "void"] == .ok false
#guard derivation.trait .isTriviallyCopyable [.ptr cB] == .ok true
#guard derivation.trait .isTriviallyCopyable [.lref cB] == .ok false
#guard derivation.trait .isStandardLayout [cD] == .ok true
#guard derivation.trait .isEmpty [cD] == .ok true
#guard derivation.trait .isEmpty [int] == .ok false

-- Standard layout.
private def twoClasses : Program :=
  [ .class "B", .member cB { name := "b", ty := int }, .class "D" [cB], .member cD { name := "d", ty := int } ]
#guard twoClasses.trait .isStandardLayout [cD] == .ok false
#guard twoClasses.trait .isStandardLayout [cB] == .ok true
private def repeated : Program :=
  [ .class "Q", .class "S" [.named "Q"], .class "T" [.named "Q"], .class "U" [.named "S", .named "T"] ]
#guard repeated.trait .isStandardLayout [.named "U"] == .ok false
#guard repeated.trait .isStandardLayout [.named "S"] == .ok true
#guard repeated.trait .isEmpty [.named "U"] == .ok true

-- Invocable.
#guard derivation.trait .isInvocable [Ty.fn' [int, .lref (.const cB)] int, int, cD] == .ok true
#guard derivation.trait .isInvocable [Ty.fn' [int] int, cD] == .ok false
#guard derivation.trait .isInvocable [.ptr (Ty.fn' [] int)] == .ok true
#guard (derivation.trait .isInvocable [cD]).isOk == false

-- A trait in a constraint is answered by the program's environment.
#guard Constraint.satisfied (Env.ofProgram derivation).atomic [(0, cD)] (.trait .isBaseOf [cB, .param 0]) == .ok true
#guard Constraint.satisfied (Env.ofProgram derivation).atomic [(0, cB)] (.trait .isBaseOf [cD, .param 0]) == .ok false
