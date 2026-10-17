-- OverloadTest/Typeclass.lean                                        -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of canonical lookup: the first example of
[temp.spec.partial.match]/2, which exercises matching and ordering with a
constant template parameter, and the two lookup theorems on a small
program. -/

open Overload Overload.PartialOrdering

private def int : Ty := .named "int"
private def char : Ty := .named "char"
private def typeParam : TemplateParam := { kind := .type }
private def intParam : TemplateParam := { kind := .const int }
private def ty (i : Nat) : Ty := .param i
private def val (i : Nat) : Ty := .value (.param i)
private def lit (n : Int) : Ty := .value (.int n)

/-! ### [temp.spec.partial.match]/2, first example

The partial specializations #2 to #5 of `A` are at positions 0 to 3. -/

private def A : List (Head × Ty) :=
  [ ([typeParam, intParam], .args [ty 0, .ptr (ty 0), val 1])                       -- #2
  , ([typeParam, typeParam, intParam], .args [.ptr (ty 0), ty 1, val 2])            -- #3
  , ([typeParam], .args [int, .ptr (ty 0), lit 5])                                  -- #4
  , ([typeParam, typeParam, intParam], .args [ty 0, .ptr (ty 1), val 2]) ]          -- #5

#guard select "A" A (.args [int, int, lit 1]) == .noMatch                -- a1 uses #1
#guard select "A" A (.args [int, .ptr int, lit 1]) == .selected 0        -- a2 uses #2
#guard select "A" A (.args [int, .ptr char, lit 5]) == .selected 2       -- a3 uses #4
#guard select "A" A (.args [int, .ptr char, lit 1]) == .selected 3       -- a4 uses #5
#guard select "A" A (.args [.ptr int, .ptr int, lit 2]) == .ambiguous [1, 3]  -- a5 is ambiguous

/-! ### Coherence and stability on a program -/

private def box (t : Ty) : Ty := .spec' "box" [t]
private def before : Program :=
  [.classTemplate "box" [typeParam], .lookup "functor", .instance "functor" [typeParam] (box (ty 0))]
private def after : Program :=
  [.classTemplate "box" [typeParam], .lookup "functor", .instance "functor" [] (box int),
   .instance "functor" [typeParam] (box (ty 0))]

-- The new instance for `box<int>` is declared before the old one, so the
-- old one moves from position 0 to 1. Lookup at `box<char>` keeps its
-- answer up to that shift; at `box<int>` it moves to the new instance.
#guard before.selectInstance "functor" (box char) == .selected 0
#guard after.selectInstance "functor" (box char) == .selected 1
#guard before.selectInstance "functor" (box int) == .selected 0
#guard after.selectInstance "functor" (box int) == .selected 0
#guard after.selectInstance "functor" int == .noMatch

example : after.selectInstance "functor" (box int) = .selected 0 ∧
    MostSpecialized "functor" (after.instancesOf "functor") (box int) 0 :=
  ⟨by decide, (coherence _ _ _ _).1 (by decide)⟩

-- `stability` instantiated at the insertion above.
example (a : Ty) := stability [.classTemplate "box" [typeParam], .lookup "functor"]
  [.instance "functor" [typeParam] (box (ty 0))] "functor" [] (box int) a
