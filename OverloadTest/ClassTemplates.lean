-- OverloadTest/ClassTemplates.lean                                   -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of class template members: the current instantiation, the
specialization key, the instantiation of member declarations, and the
member accessors and bases over a specialization. -/

open Overload

private def int : Ty := .named "int"
private def T : TemplateParam := { kind := .type }
private def N : TemplateParam := { kind := .const int }
private def box : Ty := currentInstantiation "box" [T]
private def boxOf (t : Ty) : Ty := .spec' "box" [t]

/-- `template <class T> struct box : base<T>, protected impl { T value; T get() const;
template <class U> U as(T, U) const; box(const T&); operator T() const; box(const box&) = default; };`
and a class template with a constant parameter and a default. -/
private def p : Program :=
  [ .class "impl", .classTemplate "base" [T]
  , .classTemplate "box" [T] [.spec' "base" [.param 0]] [.named "impl"]
  , .member box { name := "value", ty := .param 0 }
  , .function "get" [] [.class "box"] (ret := .param 0)
  , .functionTemplate { name := "as", head := [T], params := [.param 0, .param 1], ret := .param 1
                        scope := [.class "box"] }
  , .converting box (.constructor (.lref (.const (.param 0))))
  , .converting box (.function (.param 0))
  , .special box { kind := .copyCtor, body := .defaulted }
  , .classTemplate "arr" [T, { kind := .const int, default := some (.value (.int 3)) }]
  , .member (currentInstantiation "arr" [T, N]) { name := "size", ty := .value (.param 1) } ]

-- The current instantiation spells the head's parameters, a value for a constant one.
#guard box == .spec' "box" [.param 0]
#guard currentInstantiation "arr" [T, N] == .spec' "arr" [.param 0, .value (.param 1)]

-- The key of a class is itself; of a specialization, the current instantiation with its arguments.
#guard p.classKey? (.named "impl") == some (.named "impl", [])
#guard p.classKey? (boxOf int) == some (box, [int])
-- A default completes the argument list; an argument of the wrong kind, too many, or an
-- undeclared template give no key.
#guard p.classKey? (.spec' "arr" [int]) == some (currentInstantiation "arr" [T, N], [int, .value (.int 3)])
#guard p.classKey? (.spec' "arr" [int, .value (.int 5)]) == some (currentInstantiation "arr" [T, N], [int, .value (.int 5)])
#guard p.classKey? (.spec' "box" [.value (.int 1)]) == none
#guard p.classKey? (.spec' "box" [int, int]) == none
#guard p.classKey? (.spec' "nothing" [int]) == none

-- The members of a specialization are the template's with the argument substituted.
#guard p.membersOf (boxOf int) == [{ name := "value", ty := int }]
#guard p.membersOf (.spec' "arr" [int]) == [{ name := "size", ty := .value (.int 3) }]
#guard p.specialDecls (boxOf int) == [{ kind := .copyCtor, body := .defaulted }]
#guard p.conversionsOf (boxOf int) == [.constructor (.lref (.const int)), .function int]
-- The template's own key has the declarations as written.
#guard p.membersOf box == [{ name := "value", ty := .param 0 }]
-- A specialization that is not a key has nothing.
#guard p.membersOf (boxOf (.value (.int 1))) == []

-- The bases of a specialization are the template's, substituted, public then protected.
#guard p.directBases (boxOf int) == [.spec' "base" [int], .named "impl"]
#guard p.derives (boxOf int) (.named "impl")
#guard p.allBases (boxOf int) == [.spec' "base" [int], .named "impl"]
#guard p.directBases (.spec' "base" [int]) == []

-- A member function's parameters and return type are substituted; a member template's own
-- parameter is renumbered from zero and its constraint substituted.
#guard Decl.instantiate [int] (.function "get" [] [.class "box"] (ret := .param 0)) ==
  .function "get" [] [.class "box"] (ret := int)
#guard Decl.instantiate [int]
    (.functionTemplate { name := "as", head := [T], params := [.param 0, .param 1], ret := .param 1
                         constraint := some (.trait .isSame [.param 0, .param 1]), scope := [.class "box"] }) ==
  .functionTemplate { name := "as", head := [T], params := [int, .param 0], ret := .param 0
                      constraint := some (.trait .isSame [int, .param 0]), scope := [.class "box"] }
-- Two own parameters after two class parameters.
#guard Decl.instantiate [int, .named "char"]
    (.functionTemplate { name := "g", head := [T, T], params := [.param 1, .param 2, .param 3, .param 0] }) ==
  .functionTemplate { name := "g", head := [T, T], params := [.named "char", .param 0, .param 1, int] }
-- A declaration that is no member, and a member with no arguments, are unchanged.
#guard Decl.instantiate [int] (.class "impl") == .class "impl"
#guard Decl.instantiate [] (.function "get" [] [.class "box"] (ret := .param 0)) ==
  .function "get" [] [.class "box"] (ret := .param 0)

-- Lookup into a specialization finds the template's members instantiated; the member call
-- leads with the object.
private def getT : Ty := .param 0
#guard p.memberScope? (boxOf int) == some [.class "box"]
#guard p.memberScope? (.named "impl") == some [.class "impl"]
#guard p.memberScope? (.spec' "nothing" [int]) == none
#guard p.declarationSet p.length (boxOf int) "get" == [.function "get" [] [.class "box"] (ret := int)]
#guard p.memberSearch p.length (boxOf int) "as" ==
  .selected [.functionTemplate { name := "as", head := [T], params := [int, .param 0], ret := .param 0
                                 scope := [.class "box"] }]
#guard p.memberSearch p.length (boxOf int) "nothing" == .selected []
#guard (p.memberCallAt (Env.ofProgram p) p.length (boxOf int) "get" []).map (·.index) == .selected 0
#guard (p.memberCallAt (Env.ofProgram p) p.length (boxOf int) "as" [{ ty := int }, { ty := .named "char" }]).map (·.index)
  == .selected 0
#guard (p.memberCallAt (Env.ofProgram p) p.length (boxOf int) "as" [{ ty := .named "impl" }, { ty := int }]).map (·.index)
  == .noMatch
-- A call operator of a class template, with its implicit object parameter spelling the specialization.
private def fnT : Program :=
  [ .class "A", .classTemplate "fn" [T], .function "operator()" [getT] [.class "fn"] .none none getT ]
#guard fnT.objectCandidates fnT.length (.spec' "fn" [int]) ==
  .selected [.function "operator()" [.lref (.const (.spec' "fn" [int])), int] [.class "fn"] .none none int]
#guard (Env.full fnT).atomic (.trait .isInvocable) [.spec' "fn" [int], int] == .ok true
#guard (Env.full fnT).atomic (.trait .isInvocable) [.spec' "fn" [int], .named "A"] == .ok false
#guard Program.classCallee (.lref (.const (.spec' "fn" [int]))) == some (.spec' "fn" [int])
#guard Program.classCallee (.ptr (.spec' "fn" [int])) == none
-- The point of instantiation precedes the first declaration that mentions the specialization,
-- and the program's class templates are well-formed.
private def usesBox : Program := p ++ [.function "use" [boxOf int], .function "use2" [boxOf int]]
#guard usesBox.pointOfInstantiation (boxOf int) == some p.length
#guard usesBox.pointOfInstantiation (boxOf (.named "char")) == none
#guard usesBox.templatesWellFormed
-- A member declared after a reference to a specialization breaks the shape.
#guard !(usesBox ++ [Decl.function "late" [] [.class "box"]]).templatesWellFormed
#guard usesBox.declarationSet (p.length + 1) (boxOf int) "get" == usesBox.declarationSet p.length (boxOf int) "get"
