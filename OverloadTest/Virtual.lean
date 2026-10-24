-- OverloadTest/Virtual.lean                                          -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of virtual functions: which functions a class's objects have,
overriding, polymorphic and abstract classes, the inherited virtual
destructor, and what they do to the traits and to a call. -/

open Overload

private def cB : Ty := .named "B"
private def cD : Ty := .named "D"
private def cD2 : Ty := .named "D2"
private def int : Ty := .named "int"

/-- `struct B { virtual void f() const; void g() const; }; struct D : B { void f() const; };` -/
private def plain : Program :=
  [ .class "B", .function "f" [] [.class "B"] .virtual, .function "g" [] [.class "B"]
  , .class "D" [cB], .function "f" [] [.class "D"] ]

#guard plain.memberFunctions cB == [.function "f" [] [.class "B"] .virtual, .function "g" [] [.class "B"]]
#guard plain.virtualFunctions cB == [.function "f" [] [.class "B"] .virtual]
#guard plain.virtualFunctions cD == [.function "f" [] [.class "D"]]
#guard plain.overrides cD (.function "f" [] [.class "D"])
#guard !plain.overrides cD (.function "g" [] [.class "D"])
#guard plain.finalOverrider cD (.function "f" [] [.class "B"] .virtual) == some (.function "f" [] [.class "D"])
#guard plain.polymorphic cB && plain.polymorphic cD
#guard !plain.abstract cB
#guard !plain.virtualDtor cB
#guard plain.virtualsWellFormed
#guard plain.trait .isPolymorphic [cB] == .ok true
#guard plain.trait .isPolymorphic [.lref cB] == .ok false
#guard plain.trait .isPolymorphic [int] == .ok false
#guard plain.trait .hasVirtualDestructor [cB] == .ok false
#guard plain.trait .isTriviallyCopyable [cB] == .ok false
#guard plain.trait .isStandardLayout [cB] == .ok false
#guard plain.trait .isEmpty [cB] == .ok false
#guard plain.trait .isTriviallyDestructible [cB] == .ok false
#guard plain.trait .isTriviallyCopyConstructible [cB] == .ok false
#guard plain.trait .isCopyConstructible [cB] == .ok true
#guard plain.trait .isDefaultConstructible [cD] == .ok true
#guard plain.valueNature cB

/-- The note of [class.virtual]/3 with a pure function: `D::f(int)` hides
and does not override, `D2::f()` overrides unseen. -/
private def hidden : Program :=
  [ .class "B", .function "f" [] [.class "B"] .pure
  , .class "D" [cB], .function "f" [int] [.class "D"]
  , .class "D2" [cD], .function "f" [] [.class "D2"] ]

#guard hidden.abstract cB
#guard hidden.abstract cD
#guard !hidden.abstract cD2
#guard hidden.virtualFunctions cD == [.function "f" [] [.class "B"] .pure]
#guard !hidden.overrides cD (.function "f" [int] [.class "D"])
#guard hidden.overrides cD2 (.function "f" [] [.class "D2"])
#guard hidden.trait .isAbstract [cD] == .ok true
#guard hidden.trait .isAbstract [cD2] == .ok false
#guard hidden.trait .isConstructible [cD] == .ok false
#guard hidden.trait .isConstructible [cD2] == .ok true
#guard hidden.trait .isConvertible [cD2, cB] == .ok false
#guard hidden.trait .isConvertible [cD2, .lref (.const cB)] == .ok true

-- A call with a by-value parameter of abstract type is ill-formed; by reference it is fine.
private def calls : Program := hidden ++ [.function "g" [cB], .function "h" [.lref (.const cB)]]
#guard calls.call (Env.ofProgram calls) (calls.candidates "g") [{ ty := cD2, lvalue := true }] ==
  .illFormed "a parameter is of abstract class type"
#guard (calls.call (Env.ofProgram calls) (calls.candidates "h") [{ ty := cD2, lvalue := true }]).map (·.index) ==
  .selected 0

/-- `struct B { virtual ~B() = default; }; struct D : B {}; struct E { B b; };` -/
private def dtors : Program :=
  [ .class "B", .special cB { kind := .dtor, body := .defaulted, virt := .virtual }
  , .class "D" [cB], .class "E", .member (.named "E") { name := "b", ty := cB } ]

#guard dtors.declaredVirtualDtor cB
#guard dtors.virtualDtor cD
#guard !dtors.virtualDtor (.named "E")
#guard dtors.polymorphic cB && dtors.polymorphic cD && !dtors.polymorphic (.named "E")
#guard dtors.trait .hasVirtualDestructor [cD] == .ok true
#guard dtors.trait .isTriviallyDestructible [cD] == .ok false
#guard dtors.trait .isTriviallyDestructible [.named "E"] == .ok false
#guard dtors.trait .isPolymorphic [.named "E"] == .ok false
#guard !dtors.abstract cB

-- A pure destructor makes the class abstract; the derived class's destructor is not pure.
private def pureDtor : Program :=
  [ .class "B", .special cB { kind := .dtor, virt := .pure }, .class "D" [cB] ]
#guard pureDtor.abstract cB
#guard !pureDtor.abstract cD
#guard pureDtor.virtualDtor cD

-- Well-formedness of the virt-specifiers.
#guard !Program.virtualsWellFormed [ .class "B", .function "f" [] [.class "B"] .final, .class "D" [cB], .function "f" [] [.class "D"] ]
#guard !Program.virtualsWellFormed [ .class "B", .class "D" [cB], .function "f" [] [.class "D"] .override ]
#guard !Program.virtualsWellFormed [ .class "B", .function "f" [] [.class "B"] .virtual, .class "D" [cB], .function "f" [int] [.class "D"] .override ]
#guard Program.virtualsWellFormed [ .class "B", .function "f" [] [.class "B"] .virtual, .class "D" [cB], .function "f" [] [.class "D"] .final ]
#guard !Program.virtualsWellFormed [ .class "B", .special cB { kind := .dtor, virt := .final }, .class "D" [cB] ]
#guard !Program.virtualsWellFormed [ .class "B", .class "D" [cB], .special cD { kind := .dtor, virt := .override } ]
#guard Program.virtualsWellFormed [ .class "B", .special cB { kind := .dtor, virt := .virtual }, .class "D" [cB], .special cD { kind := .dtor, virt := .override } ]
