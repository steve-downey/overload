-- OverloadTest/Deduction.lean                                        -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of deduction on the fragment, including the draft's examples. -/

open Overload

private def int : Ty := .named "int"
private def T : Ty := .param 0
private def U : Ty := .param 1

-- The forms of [temp.deduct.type]/8.
#guard deduceTy T int [] == some [(0, int)]
#guard deduceTy (.ptr T) (.ptr int) [] == some [(0, int)]
#guard deduceTy (.lref T) (.lref int) [] == some [(0, int)]
#guard deduceTy (.rref T) (.rref int) [] == some [(0, int)]
#guard deduceTy (.const T) (.const int) [] == some [(0, int)]
#guard deduceTy (.spec' "C" [T, U]) (.spec' "C" [int, .ptr int]) [] == some [(1, .ptr int), (0, int)]
#guard deduceTy (.spec' "C" [T, .value (.param 1)]) (.spec' "C" [int, .value (.int 3)]) []
  == some [(1, .value (.int 3)), (0, int)]

-- Mismatched forms fail.
#guard deduceTy (.ptr T) int [] == none
#guard deduceTy (.spec' "C" [T]) (.spec' "D" [int]) [] == none
#guard deduceTy (.spec' "C" [T]) (.spec' "C" [int, int]) [] == none
#guard deduceTy (.named "A") (.named "B") [] == none

-- Consistency across pairs: [temp.deduct.type]/2 sentence 3.
#guard deduceTy (.spec' "C" [T, T]) (.spec' "C" [int, int]) [] == some [(0, int)]
#guard deduceTy (.spec' "C" [T, T]) (.spec' "C" [int, .ptr int]) [] == none

-- A non-deduced context contributes nothing and never fails.
#guard deduceTy (.spec' "C" [T, .nondeduced U]) (.spec' "C" [int, .ptr int]) [] == some [(0, int)]
#guard deduceTy (.nondeduced T) (.ptr int) [] == some []

-- A type parameter does not bind to a value or an argument list.
#guard deduceTy T (.value (.int 1)) [] == none
#guard deduceTy T .nil [] == none

-- A constant template argument whose subexpression mentions a parameter
-- is a non-deduced context ([temp.deduct.type]/5).
#guard deduceTy (.value (.obj' "P" [.param 1])) (.value (.obj' "P" [.int 2])) [] == some []

-- Call-site adjustments: [temp.deduct.call]/2 and /3, the draft's example.
private def constRef : List Ty := [.lref (.const T)]
#guard deduceCall constRef [{ ty := int }] [] == some [(0, int)]
#guard deduceCall constRef [{ ty := .const int, lvalue := true }] [] == some [(0, int)]
-- `template<class T> int f(T)` with a `const int` lvalue: top-level cv ignored.
#guard deduceCall [T] [{ ty := .const int, lvalue := true }] [] == some [(0, int)]
-- Forwarding references.
#guard deduceCall [.rref T] [{ ty := int, lvalue := true }] [] == some [(0, .lref int)]
#guard deduceCall [.rref T] [{ ty := int }] [] == some [(0, int)]
-- `const T&&` is not a forwarding reference: an lvalue `int` deduces `T` as
-- `int` here, and the binding of an lvalue to `const int&&` is for overload
-- resolution to reject.
#guard deduceCall [.rref (.const T)] [{ ty := int, lvalue := true }] [] == some [(0, int)]
-- `T&` with a `const int` lvalue deduces `T` as `const int`.
#guard deduceCall [.lref T] [{ ty := .const int, lvalue := true }] [] == some [(0, .const int)]
-- The more-cv-qualified alternative is for references only: `const T*`
-- against `int*` fails.
#guard deduceCall [.ptr (.const T)] [{ ty := .ptr int }] [] == none
-- A non-dependent parameter contributes nothing to deduction.
#guard deduceCall [int, T] [{ ty := .named "long" }, { ty := int }] [] == some [(0, int)]
-- A parameter with no argument (its default argument is in use) is a
-- non-deduced context; more arguments than parameters is not viable.
#guard deduceCall [T] [] [] == some []
#guard deduceCall [] [{ ty := int }] [] == none

-- Substitution after deduction collapses references.
#guard Ty.subst [(0, .lref int)] (.rref T) == .lref int
#guard Ty.subst [(0, int)] (.rref T) == .rref int
#guard Ty.subst [(0, int)] (.spec' "C" [T, .ptr T]) == .spec' "C" [int, .ptr int]
#guard Ty.subst [] T == T

-- Every parameter must end up deduced.
#guard allDeduced 2 [(0, int), (1, int)]
#guard !allDeduced 2 [(0, int)]

-- Template-argument equivalence is equality on values.
example : Val.Equivalent (.obj' "P" [.int 1, .bool true]) (.obj' "P" [.int 1, .bool true]) :=
  (Val.equivalent_iff _ _).2 rfl
example : ¬ Val.Equivalent (.obj' "P" [.int 1]) (.obj' "P" [.int 2]) :=
  fun h => by cases (Val.equivalent_iff _ _).1 h
