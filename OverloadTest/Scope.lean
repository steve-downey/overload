-- OverloadTest/Scope.lean                                            -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of correspondence, conflicts and the overload set. -/

open Overload

private def int : Ty := .named "int"
private def char : Ty := .named "char"
private def T : TemplateParam := { kind := .type }
private def f1 : Decl := .function "f" [int]
private def f2 : Decl := .function "f" [char]
private def tf : FunctionTemplate := { name := "f", head := [T], params := [.param 0] }
private def tfRet : FunctionTemplate := { tf with ret := int }
private def tfConstrained : FunctionTemplate := { tf with constraint := some (.atomic "C" [.param 0]) }
private def tfAuto : FunctionTemplate :=
  { name := "f", head := [{ kind := .const (.named "auto") }], params := [.param 0] }
private def tfConstrainedAuto : FunctionTemplate :=
  { name := "f", head := [{ kind := .const (.spec' "auto" [.named "C"]) }], params := [.param 0] }

-- Functions: the same parameter-type-list corresponds, another overload does not.
#guard corresponds f1 f1
#guard !corresponds f1 f2
#guard !corresponds f1 (.function "g" [int])

-- Function templates: equivalent heads, parameters, return type and constraints.
#guard corresponds (.functionTemplate tf) (.functionTemplate tf)
#guard !corresponds (.functionTemplate tf) (.functionTemplate tfRet)
#guard !corresponds (.functionTemplate tf) (.functionTemplate tfConstrained)
-- A type-constraint on a placeholder does not separate template heads ([temp.over.link]/6).
#guard corresponds (.functionTemplate tfAuto) (.functionTemplate tfConstrainedAuto)
-- A function and a function template of one name overload.
#guard !corresponds f1 (.functionTemplate tf)

-- A type against a variable or function does not correspond; a class template does.
#guard !corresponds (.class "f") f1
#guard !corresponds (.class "f") (.object "f")
#guard corresponds (.class "f") (.classTemplate "f" [T])
#guard corresponds (.classTemplate "f" [T]) f1
#guard corresponds (.object "f") f1
#guard corresponds (.lookup "f") (.lookupHard "f")
-- Partial specializations and uses bind no name.
#guard !corresponds (.instance "f" [T] (.param 0)) (.instance "f" [T] (.param 0))

-- Conflicts: different kinds of entity under one name.
#guard potentiallyConflict (.object "f") f1
#guard potentiallyConflict (.classTemplate "f" [T]) f1
#guard !potentiallyConflict f1 f1
#guard !potentiallyConflict (.lookup "f") (.lookupHard "f")
#guard Program.conflicts [.object "fmap", f1, .function "fmap" [int]] ==
  [(.object "fmap", .function "fmap" [int])]
#guard decide (Program.scopesWellFormed [f1, f2, .functionTemplate tf, .object "g"])
#guard !decide (Program.scopesWellFormed [.object "f", f1])

-- The overload set: one declaration per entity, the first.
#guard entities [f1, f1, f2] == [f1, f2]
#guard entities [f1, f2, f1, f2] == [f1, f2]
#guard entities [.functionTemplate tf, .functionTemplate tfConstrained, .functionTemplate tf] ==
  [.functionTemplate tf, .functionTemplate tfConstrained]
#guard Program.overloadSet [f1, .object "x", f1, f2] "f" == [f1, f2]

-- The repaired call: ambiguous over declarations, selected over entities.
#guard (resolve .text (Env.ofProgram redeclaredProgram) redeclaredProgram.ranking
  (redeclaredProgram.candidates "f") [{ ty := int }]).map (·.index) == .ambiguous [0, 1]
#guard (resolve .text (Env.ofProgram redeclaredProgram) redeclaredProgram.ranking
  (redeclaredProgram.overloadSet "f") [{ ty := int }]).map (·.index) == .selected 0
#guard (resolve .text (Env.ofProgram redeclaredProgram) redeclaredProgram.ranking
  (redeclaredProgram.overloadSet "f") [{ ty := char }]).map (·.index) == .selected 1
