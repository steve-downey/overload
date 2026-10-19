-- OverloadTest/Typeclass.lean                                        -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of the encoding's call surface: stability of a call of the
operation object as instances are declared, in the encoding's
environment. -/

open Overload Overload.Typeclass

private def int : Ty := .named "int"
private def char : Ty := .named "char"
private def typeParam : TemplateParam := { kind := .type }
private def ty (i : Nat) : Ty := .param i
private def box (t : Ty) : Ty := .spec' "box" [t]

/-! ### Stability at the call surface -/

private def pair (a b : Ty) : Ty := .spec' "pair" [a, b]
private def callProgram (extra : Program) : Program :=
  [ .class "Fn", .classTemplate "box" [typeParam], .classTemplate "pair" [typeParam, typeParam]
  , .lookup "functor", .instance "functor" [typeParam] (pair (ty 0) int) ] ++ extra ++
  [ .functionTemplate (fmapObject "functor") ]
private def callAt (p : Program) (a : Ty) : Resolution Nat :=
  (resolve .text (encodingEnv p) identityRanking (p.candidates "fmap")
    [{ ty := .named "Fn" }, { ty := a }]).map (·.index)

-- One instance for `pair<T, int>`: the operation object is selected at
-- `pair<int, int>`.
#guard callAt (callProgram []) (pair int int) == .selected 0
-- An instance for `box<T>` matches neither key: both calls keep their
-- resolution, as `call_stability` says.
#guard callAt (callProgram [.instance "functor" [typeParam] (box (ty 0))]) (pair int int) == .selected 0
#guard callAt (callProgram []) (pair char int) == .selected 0
-- An instance for `pair<int, T>` matches `pair<int, int>` and is unordered
-- with the first: the call becomes ill-formed. At `pair<char, int>` it
-- does not match, and the call is unchanged.
#guard (callAt (callProgram [.instance "functor" [typeParam] (pair int (ty 0))]) (pair int int)
  matches .illFormed _)
#guard callAt (callProgram [.instance "functor" [typeParam] (pair int (ty 0))]) (pair char int) ==
  .selected 0
-- An instance at `box<int>` makes the call at `box<int>` viable, where it
-- was not: no candidate before, the operation object after.
#guard callAt (callProgram []) (box int) == .noMatch
#guard callAt (callProgram [.instance "functor" [] (box int)]) (box int) == .selected 0
