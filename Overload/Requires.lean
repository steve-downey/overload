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
    match (p.classTemplateDecl? c).map (·.1) with
    | none => .ok false
    | some h =>
      match explicitStep env h (as.toList.getD []) >>= defaultsStep env h with
      | .ok σ => .ok (allDeduced h.length σ)
      | .soft _ => .ok false
      | .hard r => .hard r
  | .named n => .ok (fundamentalName n || (p.any fun | .class m .. => m == n | _ => false))
  | .const t | .ptr t | .lref t | .rref t => p.validType env t
  | t => .ok t.concrete

/-- What an expression requirement's expression is, once it is valid:
`decltype((E))`, and whether `E` is potentially throwing, `none` where
the fragment does not say. -/
structure Expression where
  ty : Ty
  throwing : Option Bool := none
  deriving Repr, DecidableEq, Inhabited

/-- The expression a call over candidates is, as a requirement sees it:
generation that fails hard is a hard error, outside the immediate
context; a call that is viable and well-formed is an expression whose
type is the selected function's return type, since a function call is
an lvalue, an xvalue or a prvalue as its result type is a reference or
not, so `decltype((E))` is that type; it is potentially throwing when
the selected function is or the initialization of one of its parameters
is. A call that is not viable or ill-formed is no expression. -/
@[std rule "expr.call#15" "dcl.type.decltype#1" "except.spec#6"]
def callExpression (p : Program) (env : Env) (decls : List Decl) (args : List CallArg) :
    Subst (Option Expression) :=
  match generate .text env (decls.map p.normalizeDecl) args [] with
  | .hard r => .hard r
  | _ =>
    match p.call env decls args with
    | .selected c =>
      let argsThrowing := (args.zip c.params).any fun (a, t) => p.initThrowing a t
      match c.specialization with
      | some sp => .ok (some { ty := sp.ret, throwing := some (sp.template.noexcept != some true || argsThrowing) })
      | none =>
        match decls[c.index]? with
        | some d => .ok (some { ty := (d.ret?).getD (.named "void"), throwing := some (d.throwing || argsThrowing) })
        | none => .ok (some { ty := .named "void" })
    | _ => .ok none

/-- Does a call over candidates hold as a requirement: it is an
expression. -/
def callHolds (p : Program) (env : Env) (decls : List Decl) (args : List CallArg) : Subst Bool :=
  (p.callExpression env decls args).map (·.isSome)

/-- The class type of the object a member call is on, from the type the
requirement names for it: for `remove_cvref_t<decltype(TC)>` with `TC`
bound to a lookup's variable, which forming leaves as the reference to
the lookup, the type the selected instance declares its value to have,
or the name the environment gives the value; for anything else, the
type itself. -/
@[std rule "dcl.type.decltype#1"]
def lookupValueType (p : Program) (env : Env) : Ty → Subst Ty
  | .ref (.lookup n a) | .lookup n a =>
    match p.instanceValueType? n a with
    | some v => .ok v
    | none => env.instantiate n a
  | t => .ok t.typeOfValue

/-- The object's type with its class replaced and its reference and
`const` kept. -/
def _root_.Overload.Ty.withClass (cls c : Ty) : Ty :=
  match cls with
  | .lref t => .lref (go t)
  | .rref t => .rref (go t)
  | t => go t
where
  go : Ty → Ty
    | .const _ => .const c
    | _ => c

/-- The expression a member call `declval<cls>().callee(args)` is: the
members the search finds in the object's class, each with its implicit
object parameter, resolved over the object followed by the arguments. -/
@[std rule "expr.prim.req.simple#1" "over.match.funcs.general#2" "over.match.funcs.general#3"]
def memberCallExpression (p : Program) (env : Env) (cls : Ty) (callee : String) (args : List Ty) :
    Subst (Option Expression) :=
  let c := cls.referred.stripConst
  if c.isClass then
    match p.memberSearch p.length c callee with
    | .selected ms =>
      p.callExpression env ((entities ms).map (Decl.withImplicitObject c)) (declval cls :: args.map declval)
    | _ => .ok none
  else .ok none

/-- The expression an expression requirement is, with its types already
substituted, if it is valid: a simple-requirement is the call
`callee(declval<args>()...)` at the end of the program, in the global
scope; a member call is `declval<cls>()`'s call of a member, its types
formed and the object's class read through the lookup whose value it
is, when it is one; `T{args}` is a prvalue of `T` when the braced
initialization is well-formed, whether it is potentially throwing left
unsaid. A type-requirement, a compound-requirement and a
nested-requirement are not expressions. -/
@[std rule "expr.prim.req.simple#1"]
def expression (p : Program) (env : Env) : Constraint.Requirement → Subst (Option Expression)
  | .simple callee args =>
    match p.callCandidates p.length [] callee (args.map declval) with
    | .selected (fs, as) => p.callExpression env fs as
    | .illFormed _ | .noMatch | .ambiguous _ => .ok none
  | .memberCall cls callee args => do
    let cls ← form env cls
    let args ← formAll env args
    let v ← p.lookupValueType env cls.referred.stripConst
    p.memberCallExpression env (cls.withClass v) callee args
  | .braceInit t as =>
    let formed : Subst Bool :=
      if !(t :: as).all Ty.concrete then .soft "a braced initialization of a dependent type"
      else if t.stripConst.isClass && !t.isRef then .ok (p.braceInit t.stripConst (as.map declval))
      else
        match as with
        | [] => .ok (!t.isRef && !t.isVoid && !t.isFunction)
        | [a] => .ok (match p.ics .copy (declval a) t with | none | some .ambiguous => false | some _ => true)
        | _ => .ok false
    formed.map fun b => if b then some { ty := t } else none
  | _ => .soft "the requirement is not an expression"

/-- Does a nested-requirement hold: its constraint-expression, with the
concept-ids expanded, is satisfied in the environment; not satisfied
when a substitution into it fails. -/
@[std rule "expr.prim.req.nested#1"]
def nestedHolds (p : Program) (env : Env) (c : Constraint.NestedExpr) : Subst Bool :=
  match Constraint.satisfied env.atomic [] (p.normalize c.toConstraint) with
  | .soft _ => .ok false
  | r => r

/-- Does one requirement hold, with its types already substituted? An
expression requirement holds when it is an expression; a
type-requirement when its type is valid; a compound-requirement when its
expression is one, is not potentially throwing if the noexcept-specifier
is present, and the immediately-declared constraint of the
type-constraint for `decltype((E))`, the concept applied to that type
and then the trailing arguments, is satisfied, in that order; a
nested-requirement when its constraint-expression is satisfied. -/
@[std rule "expr.prim.req.simple#1" "expr.prim.req.type#1" "expr.prim.req.compound#1"
  "expr.prim.req.nested#1" "temp.param#9"]
def requirementHolds (p : Program) (env : Env) : Constraint.Requirement → Subst Bool
  | .type t => p.validType env t
  | .compound e tc ne =>
    match p.expression env e with
    | .hard r => .hard r
    | .soft _ | .ok none => .ok false
    | .ok (some x) =>
      if ne && x.throwing != some false then
        if x.throwing.isNone then .soft "whether the expression throws is outside the fragment" else .ok false
      else
        match tc with
        | none => .ok true
        | some (c, as) => p.nestedHolds env (.conceptId c (x.ty :: as))
  | .nested c => p.nestedHolds env c
  | e => (p.expression env e).map (·.isSome)

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

/-- The expression of a member call on an object of class type is one
exactly where the call is viable and well-formed, when generating its
candidates is no hard error. -/
theorem memberCallExpression_iff (p : Program) (env : Env) (cls : Ty) (f : String) (args : List Ty)
    (hc : cls.referred.stripConst.isClass = true)
    (hgen : ∀ ms, p.memberSearch p.length cls.referred.stripConst f = .selected ms →
      ∀ r, generate .text env (((entities ms).map (Decl.withImplicitObject cls.referred.stripConst)).map
        p.normalizeDecl) (Program.declval cls :: args.map Program.declval) [] ≠ .hard r) :
    (p.memberCallExpression env cls f args).map (·.isSome) = .ok true ↔
      ∃ cand, p.memberCallOn env p.length cls.referred.stripConst (Program.declval cls) f
        (args.map Program.declval) = .selected cand := by
  simp only [Program.memberCallExpression, hc, ↓reduceIte, Program.memberCallOn]
  cases hs : p.memberSearch p.length cls.referred.stripConst f with
  | selected ms =>
    simp only [Program.callExpression]
    cases hg : generate .text env (((entities ms).map (Decl.withImplicitObject cls.referred.stripConst)).map
        p.normalizeDecl) (Program.declval cls :: args.map Program.declval) [] with
    | hard r => exact absurd hg (hgen ms hs r)
    | ok _ | soft _ =>
      cases p.call env ((entities ms).map (Decl.withImplicitObject cls.referred.stripConst))
          (Program.declval cls :: args.map Program.declval) with
      | selected cand =>
        cases hsp : cand.specialization with
        | some sp => simp [hsp, Subst.map]
        | none =>
          cases hd : ((entities ms).map (Decl.withImplicitObject cls.referred.stripConst))[cand.index]? <;>
            simp [hsp, hd, Subst.map]
      | _ => simp [Subst.map]
  | illFormed _ | noMatch | ambiguous _ => simp [Subst.map]

/-- A requirement that calls a member of a class holds exactly where the
member call is viable and well-formed, when generating its candidates is
no hard error: a probe of a member through a requires-expression says
what the call says. The object's type and the arguments are formed
already, and the object's class is a class type, not a lookup's value. -/
@[std theorem "expr.prim.req.simple#1"]
theorem member_requirement_iff_call (p : Program) (env : Env) (cls : Ty) (f : String) (args : List Ty)
    (hcls : form env cls = .ok cls) (hargs : formAll env args = .ok args)
    (hv : p.lookupValueType env cls.referred.stripConst = .ok cls.referred.stripConst)
    (hw : cls.withClass cls.referred.stripConst = cls)
    (hc : cls.referred.stripConst.isClass = true)
    (hgen : ∀ ms, p.memberSearch p.length cls.referred.stripConst f = .selected ms →
      ∀ r, generate .text env (((entities ms).map (Decl.withImplicitObject cls.referred.stripConst)).map
        p.normalizeDecl) (Program.declval cls :: args.map Program.declval) [] ≠ .hard r) :
    p.requirementHolds env (.memberCall cls f args) = .ok true ↔
      ∃ cand, p.memberCallOn env p.length cls.referred.stripConst (Program.declval cls) f
        (args.map Program.declval) = .selected cand := by
  simp only [Program.requirementHolds, Program.expression, hcls, hargs, hv, hw, Subst.bind_eq, Subst.bind_ok]
  exact memberCallExpression_iff p env cls f args hc hgen

/-- A member call on a lookup's value, `TC.f(args)` for `TC` a `const
auto&` bound to the lookup, holds as a requirement exactly where the
call on the type the selected instance declares its value to have is
viable and well-formed, the object an lvalue of `const` that type: what
the operation object's constraint asks is the member call on the
instance. -/
@[std theorem "expr.prim.req.simple#1" "over.match.funcs.general#3" "dcl.type.decltype#1"]
theorem lookup_member_requirement_iff_call (p : Program) (env : Env) (tc : String) (a : Ty) (v : Ty)
    (f : String) (args : List Ty) (hv : p.instanceValueType? tc a = some v) (hc : v.isClass = true)
    (ha : a.dependent = false) (hfa : form env a = .ok a) (hinst : ∃ t, env.instantiate tc a = .ok t)
    (hargs : formAll env args = .ok args)
    (hgen : ∀ ms, p.memberSearch p.length v f = .selected ms →
      ∀ r, generate .text env (((entities ms).map (Decl.withImplicitObject v)).map p.normalizeDecl)
        (impliedObject v :: args.map Program.declval) [] ≠ .hard r) :
    p.requirementHolds env (.memberCall (.lref (.const (.typeOf (.ref (.lookup tc a))))) f args) = .ok true ↔
      ∃ cand, p.memberCallOn env p.length v (impliedObject v) f (args.map Program.declval) = .selected cand := by
  obtain ⟨t, ht⟩ := hinst
  have hform : form env (.lref (.const (.typeOf (.ref (.lookup tc a))))) =
      .ok (.lref (.const (.ref (.lookup tc a)))) := by
    simp [form, ha, hfa, ht, Ty.collapse, formConst, Ty.isRef, Ty.typeOfValue, Ty.dependent]
  simp only [Program.requirementHolds, Program.expression, hform, hargs, Subst.bind_eq, Subst.bind_ok,
    Ty.referred, Ty.stripConst, Program.lookupValueType, hv, Ty.withClass, Ty.withClass.go]
  exact memberCallExpression_iff p env (.lref (.const v)) f args hc hgen

/-! ## A class callee

`is_invocable<Fn, Args...>` is `INVOKE(declval<Fn>(), declval<Args>()...)`
well-formed ([meta.rel]/3). For a class `Fn` the invocation is the call
`f(t1, ..., tN)` of [func.require]/1, a call on an object of class type,
which resolves over the function call operators of its class
([over.call.object]/1): a search for `operator()` in the class's scope,
then overload resolution over the arguments. The base environment
answers the trait softly, since the search and the resolution live
above it; the environment one level up answers it, as it answers a
requires-expression. -/

namespace Program

/-- The class type a callee of class type names: the referred type with
its top-level `const` stripped, when that is a class, named by a
class-name or a specialization of a class template. -/
def classCallee (f : Ty) : Option Ty :=
  let c := f.referred.stripConst
  if c.isClass then some c else none

/-- `INVOKE(declval<Fn>(), declval<Args>()...)` for a class `Fn`: `Fn`
is no pointer to member, so the invocation is the call `f(t1, ..., tN)`,
a call on an object of class type, which resolves over the function
call operators of its class and its surrogate call functions, with
`declval<Fn>()` the implied object argument. The result is the call's
expression, `none` when the class has neither, its call operators are
found ambiguously, or the call is not viable or ill-formed. -/
@[std rule "func.require#1" "over.call.object#1.sentence-1" "over.call.object#2"
  "over.call.object#3.sentence-1"]
def objectInvoke (p : Program) (env : Env) (obj : CallArg) (cls : Ty) (args : List Ty) :
    Subst (Option Expression) :=
  match p.objectCandidates p.length cls with
  | .selected cs => p.callExpression env cs (obj :: args.map declval)
  | _ => .ok none

/-- A trait as the environment one level above the program answers it:
`is_invocable` of a class callee is the call on the object being an
expression, `is_nothrow_invocable` of one that call known not to throw;
every other trait, and a callee that is not a class, is what the
environment below answers. -/
@[std rule "meta.rel#3"]
def traitAbove (p : Program) (env : Env) (q : Trait) (args : List Ty) : Subst Bool :=
  match q, args with
  | .isInvocable, f :: as =>
    match classCallee f with
    | some c => (p.objectInvoke env (declval f) c as).map (·.isSome)
    | none => env.atomic (.trait q) args
  | .isNothrowInvocable, f :: as =>
    match classCallee f with
    | some c => (p.objectInvoke env (declval f) c as).map fun
      | some x => x.throwing == some false
      | none => false
    | none => env.atomic (.trait q) args
  | _, _ => env.atomic (.trait q) args

end Program

/-- The environment a program defines, with requires-expressions
answered to a depth: at depth zero the base environment,
`Env.ofProgram`, which answers a requires-expression softly; at each
depth above, the environment below decides the calls a requirement
makes and the constraints of their candidates, so a requires-expression
nested in those, through a nested-requirement's concept or a
candidate's constraint, is answered one level down; and `is_invocable`
of a class callee, the call on the object, likewise. -/
def Env.fullWithin (p : Program) (atomics : List (String × List Ty × Bool) := [])
    (extra : Constraint.ExprOracle := fun e _ => .soft s!"unknown atomic constraint {e}")
    (traits : Trait → List Ty → Subst Bool := p.trait) : Nat → Env
  | 0 => Env.ofProgram p atomics extra traits
  | depth + 1 =>
    let below := Env.fullWithin p atomics extra traits depth
    { below with
      atomic := fun atom args =>
        match atom with
        | .requires reqs => p.requirementsHold below reqs
        | .trait q => p.traitAbove below q args
        | _ => below.atomic atom args }

/-- The environment a program defines, with requires-expressions
answered as deep as the program can nest them: a concept names only
concepts declared before it, so the program's length bounds the depth. -/
def Env.full (p : Program) (atomics : List (String × List Ty × Bool) := [])
    (extra : Constraint.ExprOracle := fun e _ => .soft s!"unknown atomic constraint {e}")
    (traits : Trait → List Ty → Subst Bool := p.trait) : Env :=
  Env.fullWithin p atomics extra traits p.length

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

/-! ## Compound requirements as simple and nested ones -/

/-- An expression requirement holds exactly when it is an expression. -/
theorem requirementHolds_expression (p : Program) (env : Env) (E : Constraint.Requirement)
    (hE : E.isExpression = true) :
    p.requirementHolds env E = (p.expression env E).map (·.isSome) := by
  cases E <;> simp_all [Program.requirementHolds, Constraint.Requirement.isExpression]

/-- A requirement that is an expression is an expression requirement. -/
theorem isExpression_of_expression (p : Program) (env : Env) (E : Constraint.Requirement) (x : Program.Expression)
    (hE : p.expression env E = .ok (some x)) : E.isExpression = true := by
  cases E <;> simp_all [Program.expression, Constraint.Requirement.isExpression]

/-- A compound-requirement with a return-type-requirement, whose
expression is one, is the simple-requirement followed by the
nested-requirement of the immediately-declared constraint of the
type-constraint for `decltype((E))`: `{ E } -> C<As...>;` is
`E; requires C<decltype((E)), As...>;`, the paragraph's own
equivalence. -/
@[std theorem "expr.prim.req.compound#1"]
theorem compound_eq_simple_nested (p : Program) (env : Env) (E : Constraint.Requirement) (x : Program.Expression)
    (hE : p.expression env E = .ok (some x)) (C : String) (as : List Ty) (rest : List Constraint.Requirement) :
    p.requirementsHold env (.compound E (some (C, as)) :: rest) =
      p.requirementsHold env (E :: .nested (.conceptId C (x.ty :: as)) :: rest) := by
  have hE' : p.requirementHolds env E = .ok true := by
    rw [requirementHolds_expression p env E (isExpression_of_expression p env E x hE), hE]; rfl
  simp only [Program.requirementsHold]
  rw [hE']
  simp only [Program.requirementHolds, hE, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- A compound-requirement without a return-type-requirement or
noexcept-specifier, `{ E };`, is the simple-requirement `E;`. -/
@[std theorem "expr.prim.req.compound#1"]
theorem compound_eq_simple (p : Program) (env : Env) (E : Constraint.Requirement)
    (hE : E.isExpression = true) (rest : List Constraint.Requirement) :
    p.requirementsHold env (.compound E :: rest) = p.requirementsHold env (E :: rest) := by
  simp only [Program.requirementsHold]
  rw [requirementHolds_expression p env E hE]
  simp only [Program.requirementHolds]
  cases p.expression env E with
  | ok o => cases o <;> simp [Subst.map]
  | soft r => simp [Subst.map]
  | hard r => simp [Subst.map]

/-- When the expression of a compound-requirement is not an expression,
the compound-requirement decides as the simple-requirement does,
whatever its noexcept-specifier and return-type-requirement: `false`
for an invalid expression, the hard error for one outside the immediate
context. -/
@[std theorem "expr.prim.req.compound#1" "expr.prim.req.general#5"]
theorem compound_invalid_eq_simple (p : Program) (env : Env) (E : Constraint.Requirement)
    (hE : E.isExpression = true) (hx : ∀ x, p.expression env E ≠ .ok (some x))
    (tc : Option (String × List Ty)) (ne : Bool) (rest : List Constraint.Requirement) :
    p.requirementsHold env (.compound E tc ne :: rest) = p.requirementsHold env (E :: rest) := by
  simp only [Program.requirementsHold]
  rw [requirementHolds_expression p env E hE]
  simp only [Program.requirementHolds]
  cases h : p.expression env E with
  | ok o =>
    cases o with
    | none => simp [Subst.map]
    | some x => exact absurd h (hx x)
  | soft r => simp [Subst.map]
  | hard r => simp [Subst.map]

/-- A compound-requirement with a noexcept-specifier does not hold when
its expression is potentially throwing. -/
@[std theorem "expr.prim.req.compound#1"]
theorem compound_noexcept_throwing (p : Program) (env : Env) (E : Constraint.Requirement) (x : Program.Expression)
    (hE : p.expression env E = .ok (some x)) (ht : x.throwing = some true) (tc : Option (String × List Ty)) :
    p.requirementHolds env (.compound E tc true) = .ok false := by
  simp [Program.requirementHolds, hE, ht]

/-! ## A class callee is the call on the object -/

/-- `is_invocable` of a class callee holds exactly where the call on the
object, `declval<Fn>()` over the class's call operators and surrogates,
is viable and well-formed, when generating the candidates is no hard
error. -/
@[std theorem "meta.rel#3"]
theorem invocable_class_iff_call (p : Program) (env : Env) (f : Ty) (c : Ty) (as : List Ty)
    (hc : Program.classCallee f = some c)
    (hgen : ∀ cs, p.objectCandidates p.length c = .selected cs →
      ∀ r, generate .text env (cs.map p.normalizeDecl) (Program.declval f :: as.map Program.declval) [] ≠ .hard r) :
    p.traitAbove env .isInvocable (f :: as) = .ok true ↔
      ∃ cand, p.objectCallAt env p.length c (Program.declval f) (as.map Program.declval) = .selected cand := by
  simp only [Program.traitAbove, hc, Program.objectInvoke, Program.objectCallAt]
  cases hs : p.objectCandidates p.length c with
  | selected cs =>
    simp only [Program.callExpression]
    cases hg : generate .text env (cs.map p.normalizeDecl) (Program.declval f :: as.map Program.declval) [] with
    | hard r => exact absurd hg (hgen cs hs r)
    | ok _ | soft _ =>
      cases p.call env cs (Program.declval f :: as.map Program.declval) with
      | selected cand =>
        cases hsp : cand.specialization with
        | some sp => simp [hsp, Subst.map]
        | none => cases hd : cs[cand.index]? <;> simp [hsp, hd, Subst.map]
      | _ => simp [Subst.map]
  | illFormed _ | noMatch | ambiguous _ => simp [Subst.map]

/-- `is_nothrow_invocable` of a class callee implies `is_invocable` of
it: the trait is the base trait and the call known not to throw. -/
@[std theorem "meta.rel#3"]
theorem nothrow_invocable_class_invocable (p : Program) (env : Env) (f : Ty) (c : Ty) (as : List Ty)
    (hc : Program.classCallee f = some c)
    (h : p.traitAbove env .isNothrowInvocable (f :: as) = .ok true) :
    p.traitAbove env .isInvocable (f :: as) = .ok true := by
  simp only [Program.traitAbove, hc] at h ⊢
  cases hx : p.objectInvoke env (Program.declval f) c as with
  | ok o => cases o <;> simp_all [Subst.map]
  | soft r => simp_all [Subst.map]
  | hard r => simp_all [Subst.map]

/-- The environment one level above the program answers `is_invocable`
of a class callee by the call on the object in the environment below,
as it answers a requires-expression there. -/
@[std theorem "meta.rel#3"]
theorem full_invocable_class (p : Program) (atomics : List (String × List Ty × Bool))
    (extra : Constraint.ExprOracle) (traits : Trait → List Ty → Subst Bool) (depth : Nat)
    (f : Ty) (c : Ty) (as : List Ty) (hc : Program.classCallee f = some c) :
    (Env.fullWithin p atomics extra traits (depth + 1)).atomic (.trait .isInvocable) (f :: as) =
      (p.objectInvoke (Env.fullWithin p atomics extra traits depth) (Program.declval f) c as).map (·.isSome) := by
  show p.traitAbove _ .isInvocable (f :: as) = _
  simp [Program.traitAbove, hc]

end Overload
