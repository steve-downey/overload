-- OverloadTest/Special.lean                                          -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of the special member functions: which a class has, which are
deleted, which are trivial, and the value nature of a class. -/

open Overload

private def cM : Ty := .named "M"
private def cX : Ty := .named "X"
private def int : Ty := .named "int"

/-- `struct X { int x; int* p; };` -/
private def flat : Program :=
  [.class "X", .member cX { name := "x", ty := int }, .member cX { name := "p", ty := .ptr int }]

#guard flat.flatClass cX
#guard (flat.special cX .defaultCtor).map (·.prov) == some .defaulted
#guard (flat.special cX .copyCtor).map (·.constParam) == some true
#guard (flat.special cX .moveCtor).map (·.constParam) == some false
#guard !flat.deleted cX .defaultCtor
#guard !flat.deleted cX .copyAssign
#guard flat.eligible cX .copyCtor
#guard flat.trivial cX .copyCtor
#guard flat.trivial cX .dtor
#guard flat.valueNature cX
#guard !flat.referenceMember cX

/-- `struct X { int& r; const int c; };` -/
private def refs : Program :=
  [.class "X", .member cX { name := "r", ty := .lref int }, .member cX { name := "c", ty := .const int }]

#guard refs.deleted cX .defaultCtor
#guard !refs.deleted cX .copyCtor
#guard !refs.deleted cX .moveCtor
#guard refs.deleted cX .copyAssign
#guard refs.deleted cX .moveAssign
#guard !refs.deleted cX .dtor
#guard refs.eligible cX .copyCtor
#guard !refs.eligible cX .copyAssign
#guard !refs.valueNature cX
#guard refs.referenceMember cX

/-- `struct X { int& r {}; };`: a default member initializer saves the
default constructor, not the assignment. -/
private def refInit : Program := [.class "X", .member cX { name := "r", ty := .lref int, init := true }]
#guard !refInit.deleted cX .defaultCtor
#guard refInit.deleted cX .copyAssign
#guard !refInit.trivial cX .defaultCtor

/-- `struct M { M(const M&) = delete; }; struct X { M m; }; struct Y { X x; };` -/
private def chain : Program :=
  [ .class "M", .special cM { kind := .copyCtor, body := .deleted }
  , .class "X", .member cX { name := "m", ty := cM }
  , .class "Y", .member (.named "Y") { name := "x", ty := cX } ]

#guard (chain.special cM .defaultCtor).isNone
#guard (chain.special cM .moveCtor).isNone
#guard chain.isDeleted cM .copyCtor
#guard chain.deleted cX .copyCtor
#guard chain.deleted cX .moveCtor
#guard chain.deleted (.named "Y") .copyCtor
#guard chain.deleted (.named "Y") .moveCtor
#guard !chain.deleted cX .dtor
#guard chain.referenceMember cX == false
#guard !chain.valueNature cX
#guard !(chain.copyInitUsable { ty := cX, lvalue := true } cX)
#guard chain.copyInitUsable { ty := cX, lvalue := true } (.lref (.const cX))
#guard chain.copyInitUsable { ty := int } int

/-- `struct M { M(const M&) = delete; M(M&&) = default; }; struct X { M m; };` -/
private def rescued : Program :=
  [ .class "M", .special cM { kind := .copyCtor, body := .deleted }
  , .special cM { kind := .moveCtor, body := .defaulted, constParam := false }
  , .class "X", .member cX { name := "m", ty := cM } ]
#guard rescued.deleted cX .copyCtor
#guard !rescued.deleted cX .moveCtor
#guard rescued.copyInitUsable { ty := cX } cX
#guard !(rescued.copyInitUsable { ty := cX, lvalue := true } cX)
#guard rescued.trivial cX .moveCtor

/-- `struct M { M(M&) {} }; struct X { M m; };`: the copy constructor's form. -/
private def nonConst : Program :=
  [ .class "M", .special cM { kind := .copyCtor, constParam := false }
  , .class "X", .member cX { name := "m", ty := cM } ]
#guard (nonConst.special cX .copyCtor).map (·.constParam) == some false
#guard !nonConst.trivial cX .copyCtor
#guard !(nonConst.copyInitUsable { ty := .const cX, lvalue := true } cX)
#guard nonConst.copyInitUsable { ty := cX, lvalue := true } cX

/-- A converting constructor is a user-declared constructor and suppresses
the default constructor; one of copy form is a copy constructor. -/
private def converting : Program :=
  [ .class "S", .class "X", .converting cX (.constructor (.lref (.const (.named "S"))))
  , .class "Y", .converting (.named "Y") (.constructor (.lref (.named "Y"))) ]
#guard (converting.special cX .defaultCtor).isNone
#guard (converting.special cX .copyCtor).map (·.prov) == some .defaulted
#guard (converting.special (.named "Y") .copyCtor) == some { kind := .copyCtor, prov := .userProvided, constParam := false }
#guard (converting.special (.named "Y") .moveCtor).isNone

-- const-default-constructible: a class whose members all have
-- initializers is; a scalar is not.
#guard refInit.constDefaultConstructibleWithin refInit.length cX
#guard !flat.constDefaultConstructibleWithin flat.length int
