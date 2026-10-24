-- OverloadTest/Ordering.lean                                         -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of partial ordering: the reference tie-breaks of
[temp.deduct.partial]/9, the gate of [temp.func.order]/8 on the plan's
tie-break probe, the example of [temp.constr.order]/5, partial
specialization matching, and a bounded search for a counterexample to
the transitivity of more-specialized. -/

open Overload Overload.PartialOrdering

private def T : Ty := .param 0
private def U : Ty := .param 1
private def int : Ty := .named "int"
private def X : Ty := .named "X"
private def typeParam : TemplateParam := { kind := .type }

/-- `template <class T> void f(params)`. -/
private def ft (params : List Ty) (c : Option Constraint := none) : FunctionTemplate :=
  { name := "f", head := [typeParam], params, constraint := c }

private def call (n : Nat) : Option Nat := some n

/-! ### [temp.deduct.partial]/9 -/

-- `f(T&)` is more specialized than `f(T&&)`.
#guard moreSpecialized (call 1) (ft [.lref T]) (ft [.rref T])
#guard !moreSpecialized (call 1) (ft [.rref T]) (ft [.lref T])
-- `f(const T&)` is more specialized than `f(T&&)` and than `f(T&)`.
#guard moreSpecialized (call 1) (ft [.lref (.const T)]) (ft [.rref T])
#guard moreSpecialized (call 1) (ft [.lref (.const T)]) (ft [.lref T])
#guard !moreSpecialized (call 1) (ft [.lref T]) (ft [.lref (.const T)])
-- `f(T*)` is more specialized than `f(T)`; `f(const T*)` than `f(T*)`.
#guard moreSpecialized (call 1) (ft [.ptr T]) (ft [T])
#guard !moreSpecialized (call 1) (ft [T]) (ft [.ptr T])
#guard moreSpecialized (call 1) (ft [.ptr (.const T)]) (ft [.ptr T])
-- `f(box<T>)` is more specialized than `f(T)`; `f(box<int>)` than `f(box<T>)`.
#guard moreSpecialized (call 1) (ft [.spec' "box" [T]]) (ft [T])
#guard moreSpecialized (call 1) (ft [.spec' "box" [int]]) (ft [.spec' "box" [T]])
-- References are stripped before deduction ([temp.deduct.partial]/5), so
-- `f(T*)` is more specialized than `f(T&)`, as it is than `f(T)`.
#guard moreSpecialized (call 1) (ft [.ptr T]) (ft [.lref T])
#guard !moreSpecialized (call 1) (ft [.lref T]) (ft [.ptr T])
-- Unrelated shapes: neither.
#guard !moreSpecialized (call 1) (ft [.ptr T]) (ft [.spec' "box" [T]])
#guard !moreSpecialized (call 1) (ft [.spec' "box" [T]]) (ft [.ptr T])
-- Identical templates: neither, by irreflexivity.
#guard !moreSpecialized (call 1) (ft [T]) (ft [T])
-- Only the parameters the call has arguments for count.
private def ft2 (params : List Ty) : FunctionTemplate :=
  { name := "f", head := [typeParam, typeParam], params }
#guard !moreSpecialized (call 1) (ft2 [T, .ptr U]) (ft2 [T, U])
#guard moreSpecialized none (ft2 [T, .ptr U]) (ft2 [T, U])
-- `f(T, T*)` against `f(T, T)`: deduction fails both ways, since one
-- parameter would have to be two things ([temp.deduct.type]/2).
#guard !moreSpecialized none (ft [T, .ptr T]) (ft [T, T])
#guard !moreSpecialized none (ft [T, T]) (ft [T, .ptr T])

/-! ### The tie-break probe -/

private def c1 : Constraint := .atomic "c1" [T]
private def c2 : Constraint := .conj (.atomic "c1" [T]) (.atomic "is_empty" [T])
private def lookupDefault : TemplateParam :=
  { kind := .const (.named "auto"), default := some (.lookup "functor" T) }
private def constrainedDefault : TemplateParam :=
  { kind := .const (.spec' "auto" [.named "shape"]), default := some (.lookup "functor" T) }

-- A: requires-clauses only; #2 is more constrained.
#guard moreSpecialized (call 1) (ft [T] c2) (ft [T] c1)
#guard !moreSpecialized (call 1) (ft [T] c1) (ft [T] c2)
-- B: an extra defaulted template parameter on #2 switches the tie-break off.
#guard !moreSpecialized (call 1)
  { name := "g", head := [typeParam, lookupDefault], params := [T], constraint := some c2 } (ft [T] c1)
-- C: a type-constraint on the auto constant parameter keeps it.
#guard moreSpecialized (call 1)
  { name := "g", head := [typeParam, constrainedDefault], params := [T], constraint := some c2 }
  { name := "g", head := [typeParam, lookupDefault], params := [T], constraint := some c2 |>.map fun _ => c1 }
#guard headsEquivalent [typeParam, constrainedDefault] [typeParam, lookupDefault]
-- D: constant parameters of different concrete types are not equivalent.
#guard !headsEquivalent
  [typeParam, { kind := .const int, default := some (.value (.int 0)) }]
  [typeParam, { kind := .const (.named "long"), default := some (.value (.int 0)) }]
#guard !moreSpecialized (call 1)
  { name := "g", head := [typeParam, { kind := .const int }], params := [T], constraint := some c2 }
  { name := "g", head := [typeParam, { kind := .const (.named "long") }], params := [T], constraint := some c1 }

/-! ### Subsumption -/

#guard Constraint.subsumes c2 c1
#guard !Constraint.subsumes c1 c2
#guard Constraint.subsumes c1 c1
#guard Constraint.subsumes (.conj (.atomic "a" []) (.atomic "b" [])) (.disj (.atomic "a" []) (.atomic "c" []))
#guard !Constraint.subsumes (.disj (.atomic "a" []) (.atomic "b" [])) (.atomic "a" [])
#guard Constraint.moreConstrained (some c2) (some c1)
#guard Constraint.moreConstrained (some c1) none
#guard !Constraint.moreConstrained none none

/-! ### [temp.constr.order]/5, the example
`template<C1 T> void f(T); // #1  template<C2 T> void f(T); // #2`, with
`C2 = C1 && *t`; `template<typename T> void g(T); // #3  template<C1 T>
void g(T); // #4`. -/

private def exampleEnv : Env :=
  { instantiate := fun _ _ => .soft "unknown"
    atomic := .ofExpr fun e args =>
      match e, args with
      | "C1", [.named "bool"] => .ok false
      | "C1", [_] => .ok true
      | "deref", [.ptr _] => .ok true
      | "deref", [_] => .ok false
      | _, _ => .soft "unknown"
    convertible := fun a t => .ok (a.ty.referred.stripConst == t.referred.stripConst) }

private def C1 : Constraint := .atomic "C1" [T]
private def C2 : Constraint := .conj (.atomic "C1" [T]) (.atomic "deref" [T])
private def fs : List Decl :=
  [ .functionTemplate { name := "f", head := [typeParam], params := [T], constraint := some C1 }
  , .functionTemplate { name := "f", head := [typeParam], params := [T], constraint := some C2 } ]
private def gs : List Decl :=
  [ .functionTemplate { name := "g", head := [typeParam], params := [T] }
  , .functionTemplate { name := "g", head := [typeParam], params := [T], constraint := some C1 } ]

private def run (decls : List Decl) (a : CallArg) : Resolution Nat :=
  (resolve .text exampleEnv identityRanking decls [a]).map (·.index)

#guard run fs { ty := int } == .selected 0                 -- f(0) selects #1
#guard run fs { ty := .ptr int } == .selected 1            -- f((int*)0) selects #2
#guard run gs { ty := .named "bool" } == .selected 0       -- g(true) selects #3
#guard run gs { ty := int } == .selected 1                 -- g(0) selects #4

/-! ### Partial specialization matching -/

private def box (t : Ty) : Ty := .spec' "box" [t]
private def boxInsts : List (Head × Ty) := [([typeParam], box T), ([], box int)]

#guard select "functor" boxInsts (box int) == .selected 1
#guard select "functor" boxInsts (box (.named "A")) == .selected 0
#guard select "functor" boxInsts int == .noMatch
#guard select "functor" [([typeParam], .spec' "pair" [T, int]), ([typeParam], .spec' "pair" [int, T])]
  (.spec' "pair" [int, int]) == .ambiguous [0, 1]
#guard select "functor" [([typeParam], .spec' "pair" [T, int]), ([typeParam], .spec' "pair" [int, T])]
  (.spec' "pair" [int, .named "A"]) == .selected 1
-- A pattern whose parameter is not deducible from the argument does not match.
#guard select "functor" [([typeParam, typeParam], box T)] (box int) == .noMatch
-- The relation form agrees.
example : PatternMatches [typeParam] (box T) (box int) := (patternMatches_iff _ _ _).2 rfl

/-! ### Transitivity, searched

More-specialized is irreflexive and asymmetric by theorem. Transitivity
is checked here over every triple of single-parameter templates drawn
from a small set of parameter types; the result is recorded by the guard
at the end, and a counterexample, if the set ever produces one, goes to
docs/findings.md. -/

private def shapes : List Ty :=
  [ T, .lref T, .rref T, .lref (.const T), .rref (.const T), .ptr T, .ptr (.const T)
  , .const T, box T, .lref (box T), box (.ptr T), box (.lref T), .ptr (box T)
  , int, .lref int, .lref (.const int), .ptr int, box int ]

private def triples : List (Ty × Ty × Ty) :=
  shapes.flatMap fun a => shapes.flatMap fun b => shapes.map fun c => (a, b, c)

/-- The triples on which transitivity fails. -/
def transitivityCounterexamples : List (Ty × Ty × Ty) :=
  triples.filter fun (a, b, c) =>
    moreSpecialized (call 1) (ft [a]) (ft [b]) && moreSpecialized (call 1) (ft [b]) (ft [c]) &&
      !moreSpecialized (call 1) (ft [a]) (ft [c])

-- 18 shapes, 5832 triples, no counterexample on 16 October 2026.
#guard shapes.length == 18
#guard transitivityCounterexamples.isEmpty

-- `moreSpecialized_trans` proves transitivity for the shapes that are
-- plain, those without a reference; the search still covers the rest.
#guard (shapes.filter Ty.plain).length == 10
example : Simple (ft [.ptr (.const T)]) where
  types := by simp [ft, typeParam]
  plain := by simp [ft, Ty.plain, T]
  inScope := by simp [ft, usedParams, T]
