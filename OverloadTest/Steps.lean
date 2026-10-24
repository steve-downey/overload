-- OverloadTest/Steps.lean                                            -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of the step order of [temp.deduct.general]/5: the paragraph's own
examples, the example of /8, and the plan's step-order hazard. -/

open Overload

private def T : Ty := .param 0
private def U : Ty := .param 1
private def int : Ty := .named "int"
private def typeParam : TemplateParam := { kind := .type }

/-- An environment in which nothing instantiates, nothing is satisfied,
and only identical types convert. -/
private def plain : Env :=
  { instantiate := fun n a => .soft s!"no {n}<{repr a}>"
    atomic := .ofExpr fun e _ => .soft s!"no {e}"
    convertible := fun a t => .ok (a.ty.referred.stripConst == t.referred.stripConst) }

private def argsOf (s : Subst Specialization) : Option (List (ParamIdx × Ty)) :=
  match s with
  | .ok sp => some (Emit.normalize sp.template.head.length sp.args)
  | _ => none

/-! ### [temp.deduct.general]/5, the first example
`template <class T, class U = double> void f(T t = 0, U u = 0);` -/

private def fDefaults : FunctionTemplate :=
  { name := "f"
    head := [typeParam, { kind := .type, default := some (.named "double") }]
    params := [T, U]
    defaultArgs := 2 }

#guard argsOf (deduceTemplate plain fDefaults [] [{ ty := int }, { ty := .named "char" }])
  == some [(0, int), (1, .named "char")]
#guard argsOf (deduceTemplate plain fDefaults [] [{ ty := int }])
  == some [(0, int), (1, .named "double")]
-- `f()`: T cannot be deduced, a soft failure.
#guard match deduceTemplate plain fDefaults [] [] with | .soft _ => true | _ => false
#guard argsOf (deduceTemplate plain fDefaults [int] []) == some [(0, int), (1, .named "double")]
#guard argsOf (deduceTemplate plain fDefaults [int, .named "char"] [])
  == some [(0, int), (1, .named "char")]
-- Too many explicit arguments is an invalid template-id.
#guard match deduceTemplate plain fDefaults [int, int, int] [] with | .soft _ => true | _ => false
-- An explicit argument of the wrong kind, likewise.
#guard match deduceTemplate plain fDefaults [.value (.int 1)] [] with | .soft _ => true | _ => false

/-! ### [temp.deduct.general]/5, the second example
`template <C T> typename Z<T>::xx f(void *, T);` where `C<T>` requires
`typename T::A`, and `Z<int>` fails to instantiate. -/

private def exampleEnv : Env :=
  { instantiate := fun n a =>
      match n, a with
      | "Z::xx", .named "A" => .ok (.named "A::x")
      | "Z::xx", _ => .hard "Z<T>::xx: T has no member x"
      | _, _ => .soft "unknown"
    atomic := .ofExpr fun e args =>
      match e, args with
      | "C", [.named "A"] => .ok true
      | "C", [_] => .ok false
      | _, _ => .soft "unknown"
    convertible := fun a t =>
      -- ZZ converts to int through its conversion function. Its conversion
      -- to void* goes through `operator T*()` with T = void, whose default
      -- template argument instantiates Z<void>, a hard error. Nothing else
      -- converts.
      if a.ty == .named "ZZ" && t == int then .ok true
      else if a.ty == .named "ZZ" && t == .ptr (.named "void") then .hard "Z<void>::xx: void has no member x"
      else .ok (a.ty.referred.stripConst == t.referred.stripConst) }

private def f1 : FunctionTemplate :=
  { name := "f"
    head := [typeParam]
    params := [.ptr (.named "void"), T]
    ret := .lookup "Z::xx" T
    constraint := some (.atomic "C" [T]) }

private def a : CallArg := { ty := .named "A", lvalue := true }
private def zz : CallArg := { ty := .named "ZZ", lvalue := true }

-- `f(1, a)`: deduction fails for #1 because there is no conversion from
-- int to void*: the non-dependent step, after the constraints passed.
#guard match deduceTemplate exampleEnv f1 [] [{ ty := int }, a] with
  | .soft r => r == "no implicit conversion to a non-dependent parameter"
  | _ => false
-- `f(zz, 42)`: deduction fails for #1 because C<int> is not satisfied.
#guard match deduceTemplate exampleEnv f1 [] [zz, { ty := int }] with
  | .soft r => r == "associated constraints not satisfied"
  | _ => false
-- Had the constraint not been there, the conversion of zz to void* would
-- have been checked, and it instantiates Z<void>, a hard error (and the
-- return type Z<int>::xx would be another): the step order is what keeps
-- the draft's example well-formed.
#guard match deduceTemplate exampleEnv { f1 with constraint := none } [] [zz, { ty := int }] with
  | .hard _ => true
  | _ => false
-- With `A`, everything succeeds and the return type is formed.
#guard match deduceTemplate exampleEnv f1 [] [{ ty := .ptr (.named "void") }, a] with
  | .ok s => s.ret == .named "A::x" && s.params == [.ptr (.named "void"), .named "A"]
  | _ => false

/-! ### [temp.deduct.general]/8, the example
`template<typename T> T* fun(T&& v); fun(i)`: forming "pointer to
reference to int" fails in the immediate context. -/

private def funPtr : FunctionTemplate := { name := "fun", head := [typeParam], params := [.rref T], ret := .ptr T }

#guard match deduceTemplate plain funPtr [] [{ ty := int, lvalue := true }] with
  | .soft r => r == "pointer to reference"
  | _ => false
#guard match deduceTemplate plain funPtr [] [{ ty := int }] with
  | .ok s => s.ret == .ptr int && s.params == [.rref int]
  | _ => false

/-! ### The step-order hazard -/

private def hazard (constrained : Bool) : FunctionTemplate :=
  { name := "f"
    head :=
      [ typeParam
      , { kind := .const (.lref (.const (.named "auto"))), default := some (.lookup "trait" T) } ]
    params := [T, int]
    constraint := if constrained then some (.atomic "has_instance" [.named "trait", T]) else none }

private def hardProgram : Program := [.class "X", .lookupHard "trait"]
private def softProgram : Program := [.class "X", .lookup "trait"]
private def withInstance : Program := [.class "X", .lookupHard "trait", .instance "trait" [] (.named "X")]
private def callX : List CallArg := [{ ty := .named "X" }, { ty := int }]

-- The hard design: the default's lookup fails hard, and that is the outcome.
#guard match deduceTemplate (Env.ofProgram hardProgram) (hazard false) [] callX with
  | .hard _ => true
  | _ => false
-- A requires-clause on the same template does not guard it.
#guard match deduceTemplate (Env.ofProgram hardProgram) (hazard true) [] callX with
  | .hard _ => true
  | _ => false
-- The soft design: the lookup succeeds with std::false_type and the
-- constraint fails softly.
#guard match deduceTemplate (Env.ofProgram softProgram) (hazard true) [] callX with
  | .soft r => r == "associated constraints not satisfied"
  | _ => false
-- With an instance declared, both designs deduce.
#guard match deduceTemplate (Env.ofProgram withInstance) (hazard true) [] callX with
  | .ok s => s.args.lookup 1 == some (.spec' "instance_of" [.named "X", .value (.int 0)])
  | _ => false

-- Forming types in the immediate context.
#guard form plain (.ptr (.lref int)) == .soft "pointer to reference"
#guard form plain (.const (.lref int)) == .ok (.lref int)
#guard form plain (.lref (.rref int)) == .ok (.lref int)
#guard form plain (.lookup "trait" T) == .ok (.lookup "trait" T)
#guard form plain (.spec' "box" [.ptr (.lref int)]) == .soft "pointer to reference"

/-! ### [temp.deduct.general]/12: the conversion of explicit arguments
`template <int> int f(int); template <signed char> int f(int);` -/

private def fInt : FunctionTemplate :=
  { name := "f", head := [{ kind := .const int }], params := [int], ret := int }
private def fSignedChar : FunctionTemplate :=
  { name := "f", head := [{ kind := .const (.named "signed char") }], params := [int], ret := int }

-- `f<1000>`: the first deduces, the second fails by narrowing, softly.
#guard argsOf (deduceTemplate plain fInt [.value (.int 1000)] [{ ty := int }]) == some [(0, .value (.int 1000))]
#guard match deduceTemplate plain fSignedChar [.value (.int 1000)] [{ ty := int }] with
  | .soft _ => true | _ => false
-- `f<1>`: both deduce.
#guard argsOf (deduceTemplate plain fSignedChar [.value (.int 1)] [{ ty := int }]) == some [(0, .value (.int 1))]
-- A default template argument converts too: `template <class T, long N = 0>` binds `0`,
-- and `template <class T, bool B = 1>` binds `true`; `template <class T, signed char C = 1000>` fails.
private def fDefaultLong : FunctionTemplate :=
  { name := "f", head := [typeParam, { kind := .const (.named "long"), default := some (.value (.int 0)) }]
    params := [T] }
private def fDefaultBool : FunctionTemplate :=
  { name := "f", head := [typeParam, { kind := .const (.named "bool"), default := some (.value (.int 1)) }]
    params := [T] }
private def fDefaultNarrow : FunctionTemplate :=
  { name := "f", head := [typeParam, { kind := .const (.named "signed char"), default := some (.value (.int 1000)) }]
    params := [T] }
#guard argsOf (deduceTemplate plain fDefaultLong [] [{ ty := int }]) == some [(0, int), (1, .value (.int 0))]
#guard argsOf (deduceTemplate plain fDefaultBool [] [{ ty := int }]) == some [(0, int), (1, .value (.bool true))]
#guard match deduceTemplate plain fDefaultNarrow [] [{ ty := int }] with | .soft _ => true | _ => false
-- The declared type may depend on an earlier parameter: `template <class T, T N>`.
private def fDependent : FunctionTemplate :=
  { name := "f", head := [typeParam, { kind := .const T }], params := [T] }
#guard argsOf (deduceTemplate plain fDependent [.named "signed char", .value (.int 1000)] [{ ty := .named "signed char" }])
  == none
#guard argsOf (deduceTemplate plain fDependent [int, .value (.int 1000)] [{ ty := int }])
  == some [(0, int), (1, .value (.int 1000))]
