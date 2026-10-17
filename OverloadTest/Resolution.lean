-- OverloadTest/Resolution.lean                                       -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of candidate generation, viability, the best viable function,
and the P3606 switch: the step-order hazard under both modes, and the
example of [temp.constr.atomic]/3. -/

open Overload

private def T : Ty := .param 0
private def int : Ty := .named "int"
private def X : Ty := .named "X"
private def typeParam : TemplateParam := { kind := .type }

private def hazard (constrained : Bool) : FunctionTemplate :=
  { name := "f"
    head :=
      [ typeParam
      , { kind := .const (.lref (.const (.named "auto"))), default := some (.lookup "functor" T) } ]
    params := [T, int]
    constraint := if constrained then some (.atomic "has_instance" [.named "functor", T]) else none }

private def hardProgram : Program :=
  [.class "X", .lookupHard "functor", .functionTemplate (hazard false), .function "f" [X, int]]
private def softProgram : Program :=
  [.class "X", .lookup "functor", .functionTemplate (hazard true), .function "f" [X, int]]
private def withInstance : Program :=
  [ .class "X", .lookupHard "functor", .instance "functor" [] X
  , .functionTemplate (hazard false), .function "f" [X, int] ]

private def run (mode : Mode) (p : Program) (args : List CallArg) : Resolution Nat :=
  (resolve mode (Env.ofProgram p) identityRanking (decls := p.candidates "f") (args := args)).map
    (·.index)

private def callX : List CallArg := [{ ty := X }, { ty := int }]
private def callXlong : List CallArg := [{ ty := X }, { ty := .named "long" }]

-- Variant A of the step-order probe: under the text the hard error in the
-- template's default is the outcome; under P3606 the non-template exact
-- match suppresses deduction and is selected.
#guard match run .text hardProgram callX with | .illFormed _ => true | _ => false
#guard run .p3606 hardProgram callX == .selected 1
-- Variant D, the soft design: the template is not viable, and the
-- non-template is selected under both modes.
#guard run .text softProgram callX == .selected 1
#guard run .p3606 softProgram callX == .selected 1
-- With an instance declared the template deduces and is viable too; the
-- non-template is preferred over a template specialization.
#guard run .text withInstance callX == .selected 1
#guard run .p3606 withInstance callX == .selected 1
-- Variant G: `long` is not an exact match for `int`, so there is no
-- perfect match, the template competes, and both modes hit the hazard.
#guard hasPerfectMatch (hardProgram.candidates "f") callXlong == false
#guard match run .text hardProgram callXlong with | .illFormed _ => true | _ => false
#guard run .text hardProgram callXlong == run .p3606 hardProgram callXlong
-- No candidate at all.
#guard run .text hardProgram [{ ty := int }, { ty := int }, { ty := int }] == .noMatch

-- Perfect matches, as the model reads P3606.
#guard perfectMatch [{ ty := X }] [X]
#guard perfectMatch [{ ty := .const X, lvalue := true }] [X]
#guard perfectMatch [{ ty := X, lvalue := true }] [.lref X]
#guard !perfectMatch [{ ty := X, lvalue := true }] [.lref (.const X)]
#guard perfectMatch [{ ty := .const X, lvalue := true }] [.lref (.const X)]
#guard perfectMatch [{ ty := X }] [.rref X]
#guard !perfectMatch [{ ty := X, lvalue := true }] [.rref X]
#guard !perfectMatch [{ ty := X }] [X, int]

-- Reference binding in the identity ranking.
#guard (identityRanking.ics { ty := X } (.lref X)) == .ok none
#guard (identityRanking.ics { ty := X } (.lref (.const X))) == .ok (some ())
#guard (identityRanking.ics { ty := X, lvalue := true } (.rref X)) == .ok none

/-! ### [temp.constr.atomic]/3, the example
`template<typename T> requires (S<T>{}) void f(T); // #1  void f(int); // #2
f(0)`: checking #1's constraint is a hard error, so the call is ill-formed
even though #2 is a better match. Under P3606 #2 is a perfect match and #1
is never deduced. -/

private def exampleEnv : Env :=
  { instantiate := fun _ _ => .soft "unknown"
    atomic := fun e _ => if e == "S" then .hard "expression S<int>{} does not have type bool" else .soft "unknown"
    convertible := fun a t => .ok (a.ty.referred.stripConst == t.referred.stripConst) }

private def constrained : Program :=
  [ .functionTemplate { name := "f", head := [typeParam], params := [T], constraint := some (.atomic "S" [T]) }
  , .function "f" [int] ]

private def runEx (mode : Mode) : Resolution Nat :=
  (resolve mode exampleEnv identityRanking (decls := constrained.candidates "f") (args := [{ ty := int }])).map
    (·.index)

#guard match runEx .text with | .illFormed _ => true | _ => false
#guard runEx .p3606 == .selected 1
