-- OverloadTest/Adl.lean                                              -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of argument-dependent lookup: associated entities and
namespaces, when the lookup applies, and what a call finds. -/

open Overload

private def int : Ty := .named "int"
private def N : Scope := [.namespace "N"]
private def M : Scope := [.namespace "M"]
private def T : TemplateParam := { kind := .type }

/-- `namespace N { struct B {}; struct S : B {}; void f(S); void f(int); }
namespace M { template <class T> struct box {}; void f(box<N::S>); }
void f(int); struct D : N::S {};` -/
private def p : Program :=
  [ .class "B" [] [] N, .class "S" [.named "B"] [] N, .function "f" [.named "S"] N
  , .function "f" [int] N
  , .classTemplate "box" [T] (scope := M), .function "f" [.spec' "box" [.named "S"]] M
  , .function "f" [int], .class "D" [.named "S"] ]

-- Associated entities: the class and its bases, through cv and pointers; none for int.
#guard p.associatedEntities (.named "S") == [.named "S", .named "B"]
#guard p.associatedEntities (.named "D") == [.named "D", .named "S", .named "B"]
#guard p.associatedEntities (.const (.ptr (.named "S"))) == [.named "S", .named "B"]
#guard p.associatedEntities int == []
#guard p.associatedEntities (.spec' "box" [.named "S"]) ==
  [.spec' "box" [.named "S"], .named "S", .named "B"]
#guard p.associatedEntities (.spec' "box" [int]) == [.spec' "box" [int]]
#guard p.associatedEntities (.spec' "unknown" [.named "S"]) == []

-- Associated namespaces, each once.
#guard p.associatedNamespaces [{ ty := .named "S" }] == [N]
#guard p.associatedNamespaces [{ ty := .named "D" }] == [[], N]
#guard p.associatedNamespaces [{ ty := .spec' "box" [.named "S"] }] == [M, N]
#guard p.associatedNamespaces [{ ty := int }] == []
#guard Scope.enclosingNamespace [.namespace "a", .class "C", .class "Inner"] == [.namespace "a"]

-- The lookup finds functions of the associated namespaces declared before the point.
#guard p.adl 8 "f" [{ ty := .named "S" }] == [.function "f" [.named "S"] N, .function "f" [int] N]
#guard p.adl 3 "f" [{ ty := .named "S" }] == [.function "f" [.named "S"] N]
#guard p.adl 8 "f" [{ ty := .spec' "box" [.named "S"] }] ==
  [ .function "f" [.spec' "box" [.named "S"]] M, .function "f" [.named "S"] N
  , .function "f" [int] N ]
#guard p.adl 8 "f" [{ ty := int }] == []

-- When it applies: not after a class member or a non-function.
#guard adlApplies []
#guard adlApplies [.function "f" [int]]
#guard !adlApplies [.object "f"]
#guard !adlApplies [.function "f" [int] [.class "C"]]
#guard !adlApplies [.function "f" [int], .object "f"]

-- The call's lookup: unqualified first, then the additions, each declaration once.
#guard p.callLookup 8 [] "f" [{ ty := .named "S" }] ==
  [.function "f" [int], .function "f" [.named "S"] N, .function "f" [int] N]
#guard p.callLookup 8 N "f" [{ ty := .named "S" }] ==
  [.function "f" [.named "S"] N, .function "f" [int] N]
#guard p.callLookup 8 [] "f" [{ ty := int }] == [.function "f" [int]]
#guard objectProgram.callLookup 5 [] "fmap" [{ ty := .named "X" }] == [.object "fmap" "fmap_fn"]

-- Calls.
#guard (p.callAt (Env.ofProgram p) 8 [] "f" [{ ty := .named "S", lvalue := true }]).map (·.index) ==
  .selected 1
#guard (p.callAt (Env.ofProgram p) 8 [] "f" [{ ty := .named "D", lvalue := true }]).map (·.index) ==
  .selected 1
#guard (p.callAt (Env.ofProgram p) 8 [] "f" [{ ty := .spec' "box" [.named "S"], lvalue := true }]).map
  (·.index) == .selected 1
#guard (p.callAt (Env.ofProgram p) 8 [] "f" [{ ty := int }]).map (·.index) == .selected 0
#guard (argdepProgram.callAt (Env.ofProgram argdepProgram) 2 [] "f"
  [{ ty := .named "S", lvalue := true }]).map (·.index) == .selected 0
#guard (freeFunctionProgram.callAt (Env.ofProgram freeFunctionProgram) 3 [] "fmap"
  [{ ty := .named "X" }]).map (·.index) == .selected 1
#guard (objectProgram.callAt (Env.ofProgram objectProgram) 5 [] "fmap" [{ ty := .named "X" }]).map
  (·.index) == .selected 0
