-- OverloadTest/Inheritance.lean                                      -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of inheritance erasure: the hypothesis of `inheritance_erasure`
holds on a call that takes instances at their deduced type, and fails on
one that names a base instance type, where erasure changes the
outcome. -/

open Overload

/-- `ExactPair`, as a Boolean. -/
private def exactPair (p : Program) (I : List String) (a : CallArg) (t : Ty) : Bool :=
  !(p.touched I a.ty.referred.stripConst || p.touched I t.referred.stripConst) ||
    a.ty.referred.stripConst == t.referred.stripConst

/-- Both hypotheses of `inheritance_erasure` for a call of `name`. -/
private def exactUse (p : Program) (I : List String) (name : String) (args : List CallArg) : Bool :=
  let decls := p.candidates name
  let atDeduction := decls.all fun
    | .functionTemplate ft => (args.zip ft.params).all fun (a, t) => t.dependent || exactPair p I a t
    | _ => true
  let atUse := match generate .text (Env.ofProgram p) decls args with
    | .ok cs => cs.all fun c => (args.zip c.params).all fun (a, t) => exactPair p I a t
    | _ => true
  atDeduction && atUse

private def outcome (p : Program) (name : String) (args : List CallArg) : Resolution Nat :=
  (resolve .text (Env.ofProgram p) p.ranking (p.candidates name) args).map (·.index)

private def T : Ty := .param 0
private def typeParam : TemplateParam := { kind := .type }
private def instances : Program :=
  [ .class "functor_i", .class "applicative_i" ["functor_i"], .class "monad_i" ["applicative_i"] ]
private def I : List String := ["applicative_i", "monad_i"]
private def monad : CallArg := { ty := .named "monad_i", lvalue := true }

-- Instances taken at their deduced type: the hypothesis holds, and the
-- outcome is the same after erasure. For a non-const lvalue the
-- forwarding reference deduces `monad_i&`, which binds less qualified.
private def deduced : Program :=
  instances ++
    [ .functionTemplate { name := "use", head := [typeParam], params := [.lref (.const T)] }
    , .functionTemplate { name := "use", head := [typeParam], params := [.rref T] } ]
#guard exactUse deduced I "use" [monad]
#guard outcome deduced "use" [monad] == outcome (deduced.eraseBases I) "use" [monad]
#guard outcome deduced "use" [monad] == .selected 1

-- A priority tag beside the instance is not touched, so it may convert.
private def tagged : Program :=
  instances ++ [.class "rank0", .class "rank1" ["rank0"]] ++
    [ .functionTemplate { name := "use", head := [typeParam], params := [.lref (.const T), .named "rank0"] }
    , .functionTemplate { name := "use", head := [typeParam], params := [.lref (.const T), .named "rank1"] } ]
private def taggedArgs : List CallArg := [monad, { ty := .named "rank1" }]
#guard exactUse tagged I "use" taggedArgs
#guard outcome tagged "use" taggedArgs == outcome (tagged.eraseBases I) "use" taggedArgs
#guard outcome tagged "use" taggedArgs == .selected 1

-- A function naming a base instance type: the hypothesis fails, and so
-- does the conclusion.
#guard !exactUse namedBase ["applicative_i"] "use" [{ ty := .named "applicative_i", lvalue := true }]
#guard !exactUse rankLeak ["monad_i"] "use" [monad]
