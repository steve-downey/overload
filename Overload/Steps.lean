-- Overload/Steps.lean                                                -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Deduction
import Overload.Program

/-!
# The step order of [temp.deduct.general]/5

Deduction for a function template runs in the order the paragraph gives,
one function per sentence, composed with `>>=` on `Subst` so that the
first failure stands:

1. explicitly specified template arguments are substituted ([temp.deduct.general]/2);
2. the function type is used for deduction from the call (sentence 1);
3. default template arguments supply what was not deduced, each
   substituted with the arguments for the preceding parameters
   (sentences 2 and 3);
4. the template parameter list is substituted (sentences 4 and 5);
5. the associated constraints are checked (sentences 6 and 7);
6. in a function call, non-dependent parameters are checked for
   convertibility (sentence 8);
7. the function type is substituted (sentences 9 and 10).

Substitution forms a type in the immediate context, where an invalid type
is a deduction failure, and may instantiate a separately instantiated
construct, where a failure is a hard error ([temp.deduct.general]/8).
What the model does not model, the environment answers: `Env` is the
oracle of the `expression-depth` decision.

The step-order theorems at the end are what the plan's step-order suspect
predicted: a hard error while substituting a default template argument is
the outcome of deduction, and a requires-clause on the same template
cannot guard it, because constraints are checked after defaults.
-/

namespace Overload

/-- The environment: what the model does not model, as oracles. -/
@[assumed "expression-depth"]
structure Env where
  /-- The result of instantiating the variable template specialization
  `name<arg>` for a ground `arg`: its value, or a failure. A separately
  instantiated construct, so a failure here is outside the immediate
  context and is `hard`. -/
  instantiate : String → Ty → Subst Ty
  /-- The atomic constraint oracle: whether an expression, with the
  substituted targets of its mapping, is valid and `true`. -/
  atomic : Constraint.Oracle
  /-- Whether an argument can be implicitly converted to a non-dependent
  parameter type. Forming the conversion can instantiate, a conversion
  function template's default argument for one, so the answer is a
  `Subst`: a `hard` is a failure outside the immediate context. -/
  convertible : CallArg → Ty → Subst Bool
  /-- The base classes of a class type, direct and indirect, for deduction
  from a derived class. -/
  bases : Bases := noBases

/-- What deduction produces: the template's arguments and its substituted
function type. -/
structure Specialization where
  template : FunctionTemplate
  args : Bindings
  params : List Ty
  ret : Ty
  deriving Repr, DecidableEq, Inhabited

/-! ## Forming a substituted type -/

/-- There are no pointers to references: forming one is an invalid type,
in the immediate context. -/
@[std rule "dcl.ref#5.sentence-1"]
def formPtr (t : Ty) : Subst Ty :=
  if t.isRef then .soft "pointer to reference" else .ok (.ptr t)

/-- Cv-qualifiers introduced through a template argument on a reference
type are ignored. -/
@[std rule "dcl.ref#1.sentence-3"]
def formConst (t : Ty) : Ty :=
  if t.isRef then t else .const t

/-- Form a substituted type. An invalid type in the immediate context is a
deduction failure; a separately instantiated construct, a `lookup` whose
argument has become ground, is handed to the environment, whose failure
is outside the immediate context. A type that still mentions template
parameters is formed as far as it goes. -/
@[std rule "temp.deduct.general#8.sentence-3"]
def form (env : Env) : Ty → Subst Ty
  | .named n => .ok (.named n)
  | .param i => .ok (.param i)
  | .const t => do return formConst (← form env t)
  | .ptr t => do formPtr (← form env t)
  | .lref t => do return Ty.collapse (.lref (← form env t))
  | .rref t => do return Ty.collapse (.rref (← form env t))
  | .spec c as => do return .spec c (← form env as)
  | .nil => .ok .nil
  | .cons a as => do return .cons (← form env a) (← form env as)
  | .value v => .ok (.value v)
  | .nondeduced t => form env t
  | .lookup n a => do
    let a ← form env a
    if a.dependent then return .lookup n a else env.instantiate n a
  | .ref (.lookup n a) => do
    -- Binding the reference instantiates the variable template
    -- specialization, whose failure is outside the immediate context; the
    -- argument is the specialization itself, whatever its value.
    let a ← form env a
    if a.dependent then return .ref (.lookup n a)
    else do
      let _ ← env.instantiate n a
      return .ref (.lookup n a)
  | .ref t => do return .ref (← form env t)
  | .removeCvref t => do
    let t ← form env t
    return if t.dependent then .removeCvref t else t.referred.stripConst
  | .typeOf t => do
    let t ← form env t
    return if t.dependent then .typeOf t else t.typeOfValue

/-- Form each of a list of types, left to right, stopping at the first
failure: substitution proceeds in lexical order and stops when a condition
that causes deduction to fail is encountered. -/
@[std rule "temp.deduct.general#7.sentence-4"]
def formAll (env : Env) : List Ty → Subst (List Ty)
  | [] => .ok []
  | t :: ts => do return (← form env t) :: (← formAll env ts)

/-! ## The steps -/

/-- Does a template argument have the kind its parameter declares? -/
def kindMatches : ParamKind → Ty → Bool
  | .type, a => a.isType
  | .const _, a => !a.isType

/-- Explicitly specified template arguments are substituted for the
corresponding template parameters. A template-id that is not valid, with
more arguments than parameters or an argument of the wrong kind, is a
deduction failure. -/
@[std rule "temp.deduct.general#2.sentence-2"]
def explicitStep (head : Head) (explicit : List Ty) : Subst Bindings :=
  go 0 explicit []
where
  go : Nat → List Ty → Bindings → Subst Bindings
    | _, [], σ => .ok σ
    | i, a :: as, σ =>
      match head[i]? with
      | some p =>
        if kindMatches p.kind a then go (i + 1) as ((i, a) :: σ)
        else .soft s!"explicit template argument {i} has the wrong kind"
      | none => .soft "more explicit template arguments than template parameters"

/-- The substituted and adjusted function type is used for deduction from
the arguments of the call. -/
@[std rule "temp.deduct.general#5.sentence-1"]
def callStep (env : Env) (params : List Ty) (args : List CallArg) (σ : Bindings) :
    Subst Bindings :=
  match deduceCall env.bases (params.map (Ty.subst σ)) args σ with
  | some σ' => .ok σ'
  | none => .soft "template argument deduction failed"

/-- A template argument neither deduced nor specified takes its parameter's
default argument, substituted with the arguments determined for the
preceding parameters; a parameter with no default is a deduction failure.
An invalid substitution is a deduction failure, and the instantiation of
a separately instantiated construct in the default is outside the
immediate context. -/
@[std rule "temp.deduct.general#5.sentence-2"]
def defaultsStep (env : Env) (head : Head) (σ : Bindings) : Subst Bindings :=
  go 0 head σ
where
  go : Nat → Head → Bindings → Subst Bindings
    | _, [], σ => .ok σ
    | i, p :: ps, σ =>
      match σ.lookup i with
      | some _ => go (i + 1) ps σ
      | none =>
        match p.default with
        | some d => do
          let a ← form env (d.subst σ)
          go (i + 1) ps ((i, a) :: σ)
        | none => .soft s!"template parameter {i} is neither deduced nor explicitly specified"

/-- All uses of template parameters in the template parameter list are
replaced: the declared type of each constant template parameter is
formed. -/
@[std rule "temp.deduct.general#5.sentence-4"]
def parameterListStep (env : Env) (head : Head) (σ : Bindings) : Subst Bindings := do
  let _ ← formAll env (head.filterMap fun p =>
    match p.kind with
    | .const ty => some (ty.subst σ)
    | .type => none)
  return σ

/-- The associated constraints are checked for satisfaction; if they are
not satisfied, type deduction fails. -/
@[std rule "temp.deduct.general#5.sentence-6"]
def constraintStep (env : Env) (constraint : Option Constraint) (σ : Bindings) : Subst Bindings :=
  match constraint with
  | none => .ok σ
  | some c => do
    if ← Constraint.satisfied env.atomic σ c then return σ
    else .soft "associated constraints not satisfied"

/-- In a function call, each function parameter that was non-dependent
before any explicit template arguments were substituted is checked
against its argument: no implicit conversion is a deduction failure. -/
@[std rule "temp.deduct.general#5.sentence-8"]
def nonDependentStep (env : Env) (params : List Ty) (args : List CallArg) (σ : Bindings) :
    Subst Bindings :=
  go params args
where
  go : List Ty → List CallArg → Subst Bindings
    | [], _ | _, [] => .ok σ
    | p :: ps, a :: as => do
      if p.dependent then go ps as
      else if ← env.convertible a p then go ps as
      else .soft "no implicit conversion to a non-dependent parameter"

/-- All uses of template parameters in the function type are replaced with
the deduced or default arguments; an invalid type is a deduction failure. -/
@[std rule "temp.deduct.general#5.sentence-9"]
def functionTypeStep (env : Env) (ft : FunctionTemplate) (σ : Bindings) : Subst Specialization := do
  let params ← formAll env (ft.params.map (Ty.subst σ))
  let ret ← form env (ft.ret.subst σ)
  return { template := ft, args := σ, params, ret }

/-- Template argument deduction for a function template, from explicit
template arguments and the arguments of a call: the steps of
[temp.deduct.general]/2 and /5 in the paragraph's order. -/
def deduceTemplate (env : Env) (ft : FunctionTemplate) (explicit : List Ty) (args : List CallArg) :
    Subst Specialization :=
  explicitStep ft.head explicit
    >>= callStep env ft.params args
    >>= defaultsStep env ft.head
    >>= parameterListStep env ft.head
    >>= constraintStep env ft.constraint
    >>= nonDependentStep env ft.params args
    >>= functionTypeStep env ft

/-! ## The step-order theorems -/

/-- A hard error while substituting a default template argument is the
outcome of deduction: nothing that follows, constraints, convertibility or
the function type, is reached. -/
theorem defaults_hard_absorbing (env : Env) (ft : FunctionTemplate) (explicit : List Ty)
    (args : List CallArg) (σ : Bindings) (r : Reason)
    (hc : (explicitStep ft.head explicit >>= callStep env ft.params args) = .ok σ)
    (hd : defaultsStep env ft.head σ = .hard r) :
    deduceTemplate env ft explicit args = .hard r := by
  unfold deduceTemplate
  rw [hc]
  simp [hd]

/-- A requires-clause on the same template cannot guard the default: the
constraints are checked after the defaults are substituted, so the
outcome is the same hard error whatever the constraint is. -/
theorem constraint_cannot_guard_default (env : Env) (ft : FunctionTemplate) (explicit : List Ty)
    (args : List CallArg) (σ : Bindings) (r : Reason) (c : Option Constraint)
    (hc : (explicitStep ft.head explicit >>= callStep env ft.params args) = .ok σ)
    (hd : defaultsStep env ft.head σ = .hard r) :
    deduceTemplate env { ft with constraint := c } explicit args = .hard r :=
  defaults_hard_absorbing env { ft with constraint := c } explicit args σ r hc hd

/-- A deduction failure at the constraint step keeps the function type from
being substituted: the step order is what makes the draft's own example
well-formed, since the return type would fail hard. -/
theorem constraint_soft_shields_function_type (env : Env) (ft : FunctionTemplate)
    (explicit : List Ty) (args : List CallArg) (σ : Bindings) (r : Reason)
    (hc : (explicitStep ft.head explicit >>= callStep env ft.params args >>= defaultsStep env ft.head
      >>= parameterListStep env ft.head) = .ok σ)
    (hk : constraintStep env ft.constraint σ = .soft r) :
    deduceTemplate env ft explicit args = .soft r := by
  unfold deduceTemplate
  rw [hc]
  simp [hk]

/-- Deduction gives a hard error only if some step did, and every step
before it succeeded: the first failure is the outcome. Explicit
substitution and deduction from the call never fail hard on this
fragment, so the first disjunct is there for the statement's shape. -/
theorem deduceTemplate_hard_iff (env : Env) (ft : FunctionTemplate) (explicit : List Ty)
    (args : List CallArg) (r : Reason) :
    deduceTemplate env ft explicit args = .hard r ↔
      (explicitStep ft.head explicit >>= callStep env ft.params args) = .hard r ∨
      ∃ σ, (explicitStep ft.head explicit >>= callStep env ft.params args) = .ok σ ∧
        (defaultsStep env ft.head σ >>= parameterListStep env ft.head
          >>= constraintStep env ft.constraint >>= nonDependentStep env ft.params args
          >>= functionTypeStep env ft) = .hard r := by
  unfold deduceTemplate
  generalize explicitStep ft.head explicit >>= callStep env ft.params args = s
  cases s with
  | ok σ => simp
  | soft _ => simp
  | hard _ => simp

end Overload
