-- OverloadTest/Types.lean                                            -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of the type categories and the structural traits. -/

open Overload

private def cA : Ty := .named "A"
private def cInt : Ty := .named "int"

-- Concrete types, and what is not one.
#guard cInt.concrete
#guard (Ty.lref (.const cA)).concrete
#guard (Ty.fn' [cInt, .lref cA] cInt).concrete
#guard (Ty.spec' "C" [cInt, .value (.int 3)]).concrete
#guard !(Ty.param 0).concrete
#guard !(Ty.named "auto").concrete
#guard !(Ty.const (.lref cInt)).concrete
#guard !(Ty.synth 0).concrete

-- Primary categories, through const.
#guard cInt.isIntegral
#guard (Ty.const cInt).isIntegral
#guard (Ty.named "bool").isIntegral
#guard !(Ty.lref cInt).isIntegral
#guard (Ty.ptr cInt).isPointer
#guard (Ty.lref cInt).isLvalueReference
#guard (Ty.rref cInt).isRvalueReference
#guard cA.isClass
#guard (Ty.spec' "C" [cInt]).isClass
#guard !cInt.isClass
#guard !(Ty.named "void").isClass
#guard (Ty.fn' [cInt] cInt).isFunction
#guard (Ty.named "void").isVoid

-- Exactly one primary category holds.
#guard cInt.primaryCategory == some .integral
#guard (Ty.const (.ptr cInt)).primaryCategory == some .pointer
#guard (Ty.fn' [] cInt).primaryCategory == some .function
#guard (Ty.named "auto").primaryCategory == none

-- Composite categories.
#guard (Ty.lref cInt).isReference
#guard !(Ty.lref cInt).isObject
#guard !(Ty.fn' [] cInt).isObject
#guard !(Ty.named "void").isObject
#guard cA.isObject
#guard (Ty.ptr cA).isScalar
#guard !cA.isScalar
#guard (Ty.named "void").isFundamental
#guard !cA.isFundamental
#guard cA.isCompound
#guard !(Ty.const cInt).isCompound

-- is_const is top-level only.
#guard (Ty.const cInt).isConst
#guard !(Ty.lref (.const cInt)).isConst
#guard !(Ty.ptr (.const cInt)).isConst

-- Transformations.
#guard (Ty.const cInt).removeConst == cInt
#guard (Ty.lref (.const cInt)).removeReference == .const cInt
#guard (Ty.rref (.const cInt)).stripCvref == cInt
#guard cInt.addLvalueReference == .lref cInt
#guard (Ty.rref cInt).addLvalueReference == .lref cInt
#guard (Ty.named "void").addLvalueReference == .named "void"

-- Traits as queries.
#guard Trait.answer .isSame [cInt, cInt] == .ok true
#guard Trait.answer .isSame [cInt, .const cInt] == .ok false
#guard Trait.answer .isClass [cA] == .ok true
#guard Trait.answer .isIntegral [.param 0] == .soft "std::is_integral_v of a dependent type"
#guard Trait.answer .isSame [cInt] == .soft "is_same takes two types"
#guard Trait.answer .isPointer [cInt, cInt] == .soft "std::is_pointer_v takes one type"

-- A trait atom in a constraint is satisfied without the oracle, and an
-- invalid one is "not satisfied".
private def noOracle : Constraint.Oracle := fun e _ => .hard s!"oracle asked about {e}"
#guard Constraint.satisfied noOracle [(0, cInt)] (.trait .isIntegral [.param 0]) == .ok true
#guard Constraint.satisfied noOracle [(0, cA)] (.trait .isIntegral [.param 0]) == .ok false
#guard Constraint.satisfied noOracle [] (.trait .isIntegral [.param 0]) == .ok false
#guard Constraint.subsumes (.conj (.trait .isClass [.param 0]) (.atomic "C" [.param 0]))
  (.trait .isClass [.param 0])
#guard !Constraint.subsumes (.trait .isClass [.param 0]) (.trait .isObject [.param 0])

-- Deduction through a function type.
#guard deduceTy (Ty.fn' [.param 0] (.param 1)) (Ty.fn' [cInt] cA) [] == some [(1, cA), (0, cInt)]
#guard deduceTy (Ty.fn' [.param 0] (.param 0)) (Ty.fn' [cInt] cA) [] == none
