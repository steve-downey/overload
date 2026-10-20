-- OverloadTest/Members.lean                                          -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of member name lookup: the lookup set and its merge, the search
in a class scope, the call on an object, and a template under another
name. -/

open Overload

private def int : Ty := .named "int"
private def T : TemplateParam := { kind := .type }
private def inClass (c : String) : Scope := [.class c]

/-- `struct A { void f(); }; struct B : A {}; struct D : B { void f(int); };
struct E : A, B {}; struct F : D, A {};` -/
private def p : Program :=
  [ .class "A", .function "f" [] (inClass "A")
  , .class "B" [.named "A"]
  , .class "D" [.named "B"], .function "f" [int] (inClass "D")
  , .class "E" [.named "A", .named "B"]
  , .class "F" [.named "D", .named "A"] ]

-- The class's own declarations are the whole result.
#guard p.declarationSet 7 "D" "f" == [.function "f" [int] (inClass "D")]
#guard p.lookupSet 7 "D" "f" == { decls := some [.function "f" [int] (inClass "D")], subobjects := [["D"]] }
#guard p.memberSearch 7 "D" "f" == .selected [.function "f" [int] (inClass "D")]
-- Found in a base, through one or two steps, with the subobject recorded.
#guard p.lookupSet 7 "B" "f" == { decls := some [.function "f" [] (inClass "A")], subobjects := [["B", "A"]] }
#guard p.memberSearch 7 "B" "f" == .selected [.function "f" [] (inClass "A")]
-- The same declarations in two subobjects are shared, and the set stays valid.
#guard p.lookupSet 7 "E" "f" ==
  { decls := some [.function "f" [] (inClass "A")], subobjects := [["E", "A"], ["E", "B", "A"]] }
-- `F : D, A` has two `A` subobjects: the direct one is not a base of `D`'s, so `D::f` hides
-- nothing there, and the declaration sets differ.
#guard (p.lookupSet 7 "F" "f").decls == none
#guard (p.lookupSet 7 "F" "f").subobjects == [["F", "D"], ["F", "A"]]
-- Nothing anywhere.
#guard p.memberSearch 7 "D" "g" == .selected []
-- Before the members are declared, nothing is found.
#guard p.memberSearch 1 "A" "f" == .selected []
-- Unrelated bases with different declarations: invalid.
#guard (ambiguousBasesProgram.lookupSet 5 "C" "x").decls == none
#guard ambiguousBasesProgram.memberSearch 5 "C" "x" matches .illFormed _

-- The merge rule on its own.
private def SA : LookupSet := { decls := some [.function "x" [] (inClass "A")], subobjects := [["C", "A"]] }
private def SB : LookupSet := { decls := some [.function "x" [int] (inClass "B")], subobjects := [["C", "B"]] }
private def SAB : LookupSet := { decls := some [.function "x" [] (inClass "A")], subobjects := [["C", "B", "A"]] }
private def SD : LookupSet := { decls := some [.function "x" [int] (inClass "D")], subobjects := [["F", "D"]] }
private def SDA : LookupSet := { decls := some [.function "x" [] (inClass "A")], subobjects := [["F", "D", "A"]] }
#guard LookupSet.empty.merge SA == SA
#guard SA.merge LookupSet.empty == SA
-- Unrelated subobjects, different declarations: invalid.
#guard (SA.merge SB).decls == none
-- Unrelated subobjects, the same declarations: shared.
#guard SA.merge SAB == { decls := some [.function "x" [] (inClass "A")], subobjects := [["C", "A"], ["C", "B", "A"]] }
-- A set found in a base subobject of one already found is hidden, whichever is merged into which.
#guard SD.merge SDA == SD
#guard SDA.merge SD == SD

-- A call on an object resolves over its class's call operators.
private def q : Program :=
  [ .class "fn", .function "operator()" [int] (inClass "fn"), .object "f" "fn"
  , .class "X", .function "f" [.named "X"] [.namespace "N"] ]
#guard q.callOperators 5 "fn" == .selected [.function "operator()" [int] (inClass "fn")]
#guard q.callCandidates 5 [] "f" [{ ty := int }] == .selected [.function "operator()" [int] (inClass "fn")]
#guard (q.callAt (Env.ofProgram q) 5 [] "f" [{ ty := int }]).map (·.index) == .selected 0
#guard (q.callAt (Env.ofProgram q) 5 [] "f" [{ ty := .named "X" }]).map (·.index) == .noMatch
-- A member call.
#guard (p.memberCallAt (Env.ofProgram p) 7 "D" "f" [{ ty := int }]).map (·.index) == .selected 0
#guard (p.memberCallAt (Env.ofProgram p) 7 "D" "f" []).map (·.index) == .noMatch
#guard (p.memberCallAt (Env.ofProgram p) 7 "B" "f" []).map (·.index) == .selected 0
#guard (ambiguousBasesProgram.memberCallAt (Env.ofProgram ambiguousBasesProgram) 5 "C" "x" [])
  matches .illFormed _

-- A template under another name deduces and resolves the same.
private def ft : FunctionTemplate := { name := "f", head := [T], params := [.param 0] }
#guard (deduceTemplate (Env.ofProgram []) (ft.at "operator()" (inClass "fn")) [] [{ ty := int }]).map
  (·.args) == (deduceTemplate (Env.ofProgram []) ft [] [{ ty := int }]).map (·.args)
#guard (resolve .text (Env.ofProgram []) identityRanking [.functionTemplate (ft.at "operator()" (inClass "fn"))]
  [{ ty := int }]).map (·.index) == .selected 0
