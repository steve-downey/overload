-- Overload/Requires.lean                                             -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Members
import Overload.Environment
import Overload.Traits

/-!
# Requires-expressions

A requires-expression is an atomic constraint whose requirements the
environment decides ([expr.prim.req.general]/5): a simple-requirement is
a call that must be viable and well-formed, a type-requirement a type
that must be valid, checked in lexical order, an invalid one making the
expression `false` and never the program ill-formed, a hard error
outside the immediate context staying hard.

A call is resolved by the program's lookup, which lives above the
environment a program defines, so `Env.full` is that environment with
the requires-expressions answered: the base environment decides the
call's deduction and the constraints of the candidates, a
requires-expression inside those answered softly, one level down.
-/

namespace Overload

namespace Program

/-- Is a template-id a valid type: its class template is declared, its
arguments match the template's parameters and the remaining parameters'
default arguments are formed, by the explicit-argument and default
steps ([temp.names]/13), every parameter then having an argument. A
class name is valid when declared or fundamental; any other concrete
type is valid. -/
@[std rule "expr.prim.req.type#1" "temp.names#13"]
def validType (p : Program) (env : Env) : Ty → Subst Bool
  | .spec c as =>
    match p.findSome? (fun | .classTemplate n h _ => if n == c then some h else none | _ => none) with
    | none => .ok false
    | some h =>
      match explicitStep env h (as.toList.getD []) >>= defaultsStep env h with
      | .ok σ => .ok (allDeduced h.length σ)
      | .soft _ => .ok false
      | .hard r => .hard r
  | .named n => .ok (fundamentalName n || (p.any fun | .class m .. => m == n | _ => false))
  | .const t | .ptr t | .lref t | .rref t => p.validType env t
  | t => .ok t.concrete

/-- Does a call over candidates hold as a requirement: generation that
fails hard is a hard error, outside the immediate context; otherwise the
call is viable and well-formed, or it is not. -/
def callHolds (p : Program) (env : Env) (decls : List Decl) (args : List CallArg) : Subst Bool :=
  match generate .text env (decls.map p.normalizeDecl) args [] with
  | .hard r => .hard r
  | _ =>
    match p.call env decls args with
    | .selected _ => .ok true
    | _ => .ok false

/-- Does one requirement hold, with its types already substituted? A
simple-requirement is the call `callee(declval<args>()...)` at the end of
the program, in the global scope; a member call is `declval<cls>()`'s
call of a member; a type-requirement is a valid type. -/
@[std rule "expr.prim.req.simple#1" "expr.prim.req.type#1"]
def requirementHolds (p : Program) (env : Env) : Constraint.Requirement → Subst Bool
  | .simple callee args =>
    match p.callCandidates p.length [] callee (args.map declval) with
    | .selected fs => p.callHolds env fs (args.map declval)
    | .illFormed _ | .noMatch | .ambiguous _ => .ok false
  | .memberCall cls callee args =>
    match cls.referred.stripConst with
    | .named c =>
      match p.memberSearch p.length c callee with
      | .selected ms => p.callHolds env (entities ms) (args.map declval)
      | _ => .ok false
    | _ => .ok false
  | .type t => p.validType env t

/-- A requires-expression holds when each requirement does, checked in
lexical order and stopping at the first that decides: an invalid one is
`false`, a hard error is hard. -/
@[std rule "expr.prim.req.general#5"]
def requirementsHold (p : Program) (env : Env) : List Constraint.Requirement → Subst Bool
  | [] => .ok true
  | r :: rest =>
    match p.requirementHolds env r with
    | .ok true => p.requirementsHold env rest
    | .ok false | .soft _ => .ok false
    | .hard e => .hard e

end Program

/-- A requirement that calls a member of a class holds exactly where the
member call is viable and well-formed, when generating its candidates is
no hard error: a probe of a member through a requires-expression says
what the call says. -/
@[std theorem "expr.prim.req.simple#1"]
theorem member_requirement_iff_call (p : Program) (env : Env) (c f : String) (args : List Ty)
    (hgen : ∀ ms, p.memberSearch p.length c f = .selected ms →
      ∀ r, generate .text env ((entities ms).map p.normalizeDecl) (args.map Program.declval) [] ≠ .hard r) :
    p.requirementHolds env (.memberCall (.named c) f args) = .ok true ↔
      ∃ cand, p.memberCallAt env p.length c f (args.map Program.declval) = .selected cand := by
  simp only [Program.requirementHolds, Ty.referred, Ty.stripConst, Program.memberCallAt]
  cases hs : p.memberSearch p.length c f with
  | selected ms =>
    simp only [Program.callHolds]
    cases hg : generate .text env ((entities ms).map p.normalizeDecl) (args.map Program.declval) [] with
    | hard r => exact absurd hg (hgen ms hs r)
    | ok _ | soft _ =>
      cases p.call env (entities ms) (args.map Program.declval) <;> simp
  | illFormed _ | noMatch | ambiguous _ => simp

/-- The environment a program defines, with requires-expressions
answered: the base environment, `Env.ofProgram`, decides the calls a
requirement makes and the constraints of their candidates, so a
requires-expression nested in those is answered softly, one level down. -/
def Env.full (p : Program) (atomics : List (String × List Ty × Bool) := [])
    (extra : Constraint.ExprOracle := fun e _ => .soft s!"unknown atomic constraint {e}")
    (traits : Trait → List Ty → Subst Bool := p.trait) : Env :=
  let base := Env.ofProgram p atomics extra traits
  { base with
    atomic := fun atom args =>
      match atom with
      | .requires reqs => p.requirementsHold base reqs
      | _ => base.atomic atom args }

/-- A requires-expression is never a substitution failure of its own: an
invalid requirement is `false`. -/
@[std theorem "expr.prim.req.general#5"]
theorem requires_soft_is_false (p : Program) (env : Env) (reqs : List Constraint.Requirement)
    (r : Reason) : p.requirementsHold env reqs ≠ .soft r := by
  induction reqs with
  | nil => simp [Program.requirementsHold]
  | cons q rest ih =>
    simp only [Program.requirementsHold]
    split <;> simp_all

/-- The requirements are checked in lexical order and the check stops at
the first that decides: with every earlier requirement holding, a
requirement that does not makes the expression `false`, whatever
follows. -/
@[std theorem "expr.prim.req.general#5"]
theorem requires_false_stops (p : Program) (env : Env) (pre post : List Constraint.Requirement)
    (q : Constraint.Requirement) (hpre : ∀ r ∈ pre, p.requirementHolds env r = .ok true)
    (hq : p.requirementHolds env q = .ok false ∨ ∃ e, p.requirementHolds env q = .soft e) :
    p.requirementsHold env (pre ++ q :: post) = .ok false := by
  induction pre with
  | nil =>
    simp only [List.nil_append, Program.requirementsHold]
    rcases hq with h | ⟨e, h⟩ <;> simp [h]
  | cons r rs ih =>
    have hr := hpre r (List.mem_cons_self ..)
    simp only [List.cons_append, Program.requirementsHold, hr]
    exact ih fun x hx => hpre x (List.mem_cons_of_mem _ hx)

/-- With every earlier requirement holding, a requirement that is a hard
error makes the expression that error, whatever follows. -/
@[std theorem "expr.prim.req.general#5"]
theorem requires_hard_stops (p : Program) (env : Env) (pre post : List Constraint.Requirement)
    (q : Constraint.Requirement) (e : Reason) (hpre : ∀ r ∈ pre, p.requirementHolds env r = .ok true)
    (hq : p.requirementHolds env q = .hard e) :
    p.requirementsHold env (pre ++ q :: post) = .hard e := by
  induction pre with
  | nil => simp [Program.requirementsHold, hq]
  | cons r rs ih =>
    have hr := hpre r (List.mem_cons_self ..)
    simp only [List.cons_append, Program.requirementsHold, hr]
    exact ih fun x hx => hpre x (List.mem_cons_of_mem _ hx)

end Overload
