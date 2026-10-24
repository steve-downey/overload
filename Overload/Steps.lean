-- Overload/Steps.lean                                                -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Deduction
import Overload.Program
import Overload.Arguments

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
  /-- The value of the candidate initializer `constexpr T v = A;` for a
  class value `A` supplied to a constant template parameter of a class
  type `T` other than `A`'s own: the `T` base subobject of a derived
  value, or the object a converting constructor or conversion function
  makes ([temp.arg.nontype]/3). `Env.ofProgram` computes it as
  `Program.candidateInitializer`. -/
  initializer : Ty → Val → Option Val := fun _ _ => none

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
  | .synth i => .ok (.synth i)
  | .param i => .ok (.param i)
  | .const t => do return formConst (← form env t)
  | .ptr t => do formPtr (← form env t)
  | .lref t => do return Ty.collapse (.lref (← form env t))
  | .rref t => do return Ty.collapse (.rref (← form env t))
  | .spec c as => do return .spec c (← form env as)
  | .nil => .ok .nil
  | .cons a as => do return .cons (← form env a) (← form env as)
  | .fn ps r => do return .fn (← form env ps) (← form env r)
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
  | .enableIf c as t => do
    -- The condition is asked of the oracle with its arguments as
    -- substituted, the way satisfaction asks of a constraint's mapping.
    -- Forming the type happens once its arguments are known.
    let t ← form env t
    match env.atomic c (as.toList.getD []) with
    | .ok true => .ok t
    | .ok false => .soft s!"enable_if condition {c} is false"
    | .soft r => .soft r
    | .hard r => .hard r

/-- Form each of a list of types, left to right, stopping at the first
failure: substitution proceeds in lexical order and stops when a condition
that causes deduction to fail is encountered. -/
@[std rule "temp.deduct.general#7.sentence-4"]
def formAll (env : Env) : List Ty → Subst (List Ty)
  | [] => .ok []
  | t :: ts => do return (← form env t) :: (← formAll env ts)

/-! ## The steps -/

/-- Does a template argument have the kind its parameter declares: the
type and form of a template argument shall match those of its
parameter. -/
@[std rule "temp.arg.general#1.sentence-1"]
def kindMatches : ParamKind → Ty → Bool
  | .type, a => a.isType
  | .const _, a => !a.isType

/-- Explicitly specified template arguments are substituted for the
corresponding template parameters. A template-id that is not valid, with
more arguments than parameters, an argument of the wrong kind, or an
argument that does not convert to its parameter's type, is a deduction
failure. The parameter's declared type is substituted with the
preceding explicit arguments before the conversion ([temp.names]/13). -/
@[std rule "temp.deduct.general#2.sentence-2"]
def explicitStep (env : Env) (head : Head) (explicit : List Ty) : Subst Bindings :=
  go 0 explicit []
where
  go : Nat → List Ty → Bindings → Subst Bindings
    | _, [], σ => .ok σ
    | i, a :: as, σ =>
      match head[i]? with
      | some p =>
        if kindMatches p.kind a then
          match convertArg env.initializer σ p.kind a with
          | .ok a' => go (i + 1) as ((i, a') :: σ)
          | .soft r => .soft r
          | .hard r => .hard r
        else .soft s!"explicit template argument {i} has the wrong kind"
      | none => .soft "more explicit template arguments than template parameters"

attribute [std rule "temp.names#13"] explicitStep.go

/-- The substituted and adjusted function type is used for deduction from
the arguments of the call. -/
@[std rule "temp.deduct.general#5.sentence-1"]
def callStep (env : Env) (params : List Ty) (args : List CallArg) (σ : Bindings) :
    Subst Bindings :=
  match deduceCall env.bases (params.map (Ty.subst σ)) args σ with
  | some σ' => .ok σ'
  | none => .soft "template argument deduction failed"

/-- Deduction from the arguments of a call never consults an implicit
conversion: the three differences it allows between the deduced and the
actual argument type are cv-qualification under a reference, pointer
conversions and a derived class, so changing which conversions exist,
user-defined ones among them, changes no deduced binding. Conversions
enter later, at the check of the non-dependent parameters. -/
@[std theorem "temp.deduct.call#4"]
theorem deduction_ignores_conversion (env : Env) (convertible : CallArg → Ty → Subst Bool)
    (params : List Ty) (args : List CallArg) (σ : Bindings) :
    callStep { env with convertible } params args σ = callStep env params args σ := rfl

/-- A template argument neither deduced nor specified takes its parameter's
default argument, substituted with the arguments determined for the
preceding parameters; a parameter with no default is a deduction failure.
An invalid substitution is a deduction failure, and the instantiation of
a separately instantiated construct in the default is outside the
immediate context. A constant parameter's default is a template
argument for it, and converts to the parameter's type as an explicit
one does ([temp.arg.nontype]/1); a type parameter's default is a type.
-/
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
          let a ← match p.kind with
            | .type => pure a
            | .const _ => convertArg env.initializer σ p.kind a
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
  explicitStep env ft.head explicit
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
    (hc : (explicitStep env ft.head explicit >>= callStep env ft.params args) = .ok σ)
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
    (hc : (explicitStep env ft.head explicit >>= callStep env ft.params args) = .ok σ)
    (hd : defaultsStep env ft.head σ = .hard r) :
    deduceTemplate env { ft with constraint := c } explicit args = .hard r :=
  defaults_hard_absorbing env { ft with constraint := c } explicit args σ r hc hd

/-- A deduction failure at the constraint step keeps the function type from
being substituted: the step order is what makes the draft's own example
well-formed, since the return type would fail hard. -/
theorem constraint_soft_shields_function_type (env : Env) (ft : FunctionTemplate)
    (explicit : List Ty) (args : List CallArg) (σ : Bindings) (r : Reason)
    (hc : (explicitStep env ft.head explicit >>= callStep env ft.params args >>= defaultsStep env ft.head
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
      (explicitStep env ft.head explicit >>= callStep env ft.params args) = .hard r ∨
      ∃ σ, (explicitStep env ft.head explicit >>= callStep env ft.params args) = .ok σ ∧
        (defaultsStep env ft.head σ >>= parameterListStep env ft.head
          >>= constraintStep env ft.constraint >>= nonDependentStep env ft.params args
          >>= functionTypeStep env ft) = .hard r := by
  unfold deduceTemplate
  generalize explicitStep env ft.head explicit >>= callStep env ft.params args = s
  cases s with
  | ok σ => simp
  | soft _ => simp
  | hard _ => simp

/-! ## Lemmas about the steps

What the steps do on the shapes a call presents, and what an `ok` outcome
of a step says about its bindings. These serve the theorems about
particular templates, on both sides of the model. -/

/-- A type that forming leaves as it is: no reference, pointer or
`const` applied to a reference, and none of the constructs forming
computes or instantiates. -/
def Ty.formed : Ty → Bool
  | .named _ | .nil | .value _ | .param _ => true
  | .const t | .ptr t | .lref t | .rref t => t.formed && !t.isRef
  | .spec _ as => as.formed
  | .cons a as => a.formed && as.formed
  | _ => false

theorem form_formed (env : Env) (t : Ty) (h : t.formed = true) : form env t = .ok t := by
  induction t with
  | named _ | nil | value _ | param _ => rfl
  | const t ih =>
    simp only [Ty.formed, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp [form, ih h.1, formConst, h.2]
  | ptr t ih =>
    simp only [Ty.formed, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp [form, ih h.1, formPtr, h.2]
  | lref t ih | rref t ih =>
    simp only [Ty.formed, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [form, ih h.1, Subst.bind_eq, Subst.bind_ok, Subst.pure_eq]
    cases t <;> simp_all [Ty.collapse, Ty.isRef]
  | spec c as ih =>
    simp only [Ty.formed] at h
    simp [form, ih h]
  | cons a as iha ihas =>
    simp only [Ty.formed, Bool.and_eq_true] at h
    simp [form, iha h.1, ihas h.2]
  | _ => simp [Ty.formed] at h

theorem formed_stripConst (t : Ty) (h : t.formed = true) : t.stripConst.formed = true := by
  cases t <;> simp_all [Ty.stripConst, Ty.formed]

theorem dependent_stripConst (t : Ty) : t.stripConst.dependent = t.dependent := by
  cases t <;> rfl

/-- The type a forwarding reference deduces from an argument: the
argument's type, as an lvalue reference for an lvalue. -/
def forwarded (a : CallArg) : Ty := if a.lvalue then .lref a.ty else a.ty

theorem forwarded_formed (a : CallArg) (h : a.ty.formed = true) (hr : a.ty.isRef = false) :
    (forwarded a).formed = true := by
  unfold forwarded
  split <;> simp [Ty.formed, h, hr]

theorem forwarded_key (a : CallArg) (hr : a.ty.isRef = false) :
    (forwarded a).referred.stripConst = a.ty.stripConst := by
  unfold forwarded
  split
  · rfl
  · cases h : a.ty <;> simp_all [Ty.referred, Ty.isRef]

theorem forwarded_dependent (a : CallArg) : (forwarded a).dependent = a.ty.dependent := by
  unfold forwarded
  split <;> rfl

theorem forwarded_isType (a : CallArg) (h : a.ty.isType = true) : (forwarded a).isType = true := by
  unfold forwarded
  split
  · rfl
  · exact h

theorem collapse_rref_forwarded_formed (a : CallArg) (h : a.ty.formed = true)
    (hr : a.ty.isRef = false) : (Ty.collapse (.rref (forwarded a))).formed = true := by
  unfold forwarded
  split
  · simp [Ty.collapse, Ty.formed, h, hr]
  · cases ha : a.ty <;> simp_all [Ty.collapse, Ty.formed, Ty.isRef]

/-- A parameter bound to a type is replaced by it. -/
theorem subst_param_type (σ : Bindings) (i : ParamIdx) (t : Ty) (hl : σ.lookup i = some t)
    (ht : t.isType = true) : Ty.subst σ (.param i) = t := by
  simp only [Ty.subst, hl]
  split <;> simp_all [Ty.isType]

/-- More arguments than parameters: deduction fails at the call, whatever
the environment. -/
theorem deduceCall_too_many (b : Bases) :
    ∀ (ps : List Ty) (as : List CallArg) (σ : Bindings), ps.length < as.length → deduceCall b ps as σ = none
  | [], _ :: _, _, _ => rfl
  | p :: ps, a :: as, σ, h => by
    simp only [deduceCall]
    cases deduceParam b p a σ with
    | none => rfl
    | some σ' => exact deduceCall_too_many b ps as σ' (by simpa using h)

theorem deduceTemplate_too_many (env : Env) (ft : FunctionTemplate) (args : List CallArg)
    (h : ft.params.length < args.length) :
    deduceTemplate env ft [] args = .soft "template argument deduction failed" := by
  simp only [deduceTemplate, explicitStep, explicitStep.go, Subst.bind_eq, Subst.bind_ok, callStep]
  rw [deduceCall_too_many _ _ _ _ (by simpa using h)]
  rfl

/-- No explicit arguments: no bindings. -/
@[simp]
theorem explicitStep_nil (env : Env) (head : Head) : explicitStep env head [] = .ok [] := rfl

/-- Substituting explicit arguments never fails outside the immediate
context: an invalid template-id is a deduction failure, and so is a
conversion that fails. -/
theorem explicitStep_not_hard (env : Env) (head : Head) (explicit : List Ty) (r : Reason) :
    explicitStep env head explicit ≠ .hard r := by
  simp only [explicitStep]
  suffices ∀ (as : List Ty) i σ, explicitStep.go env head i as σ ≠ .hard r from this _ _ _
  intro as
  induction as with
  | nil => intro i σ; simp [explicitStep.go]
  | cons a as ih =>
    intro i σ
    simp only [explicitStep.go]
    cases head[i]? with
    | none => simp
    | some p =>
      dsimp only
      split
      · cases hc : convertArg env.initializer σ p.kind a with
        | ok a' => exact ih _ _
        | soft _ => simp
        | hard r' => exact absurd hc (convertArg_not_hard _ _ _ _ r')
      · simp

/-- A conversion failure of an explicit template argument is soft, and it
is the outcome of deduction: it comes before deduction from the call,
the defaults, the constraints and the function type, so no hard error
of theirs is reached. -/
theorem conversion_soft_shields_call (env : Env) (ft : FunctionTemplate) (explicit : List Ty)
    (args : List CallArg) (r : Reason) (h : explicitStep env ft.head explicit = .soft r) :
    deduceTemplate env ft explicit args = .soft r := by
  unfold deduceTemplate
  rw [h]
  rfl

/-- Two explicit arguments with one converted value, in the same place,
give one bindings list: the specialization is named by the parameter
values the arguments determine, not by the arguments. -/
@[std theorem "temp.type#1"]
theorem explicitStep_converted (env : Env) (p : TemplateParam) (ps : Head) (a b : Ty)
    (rest : List Ty) (hk : kindMatches p.kind a = kindMatches p.kind b)
    (hc : convertArg env.initializer [] p.kind a = convertArg env.initializer [] p.kind b) :
    explicitStep env (p :: ps) (a :: rest) = explicitStep env (p :: ps) (b :: rest) := by
  simp only [explicitStep, explicitStep.go, List.getElem?_cons_zero, hk, hc]

/-- The template parameter list step keeps the bindings. -/
theorem parameterListStep_ok (env : Env) (h : Head) (σ σ' : Bindings)
    (e : parameterListStep env h σ = .ok σ') : σ' = σ := by
  simp only [parameterListStep, Subst.bind_eq] at e
  revert e
  generalize formAll env _ = r
  intro e
  cases r with
  | ok _ => simp only [Subst.bind_ok, Subst.pure_eq, Subst.ok.injEq] at e; exact e.symm
  | soft _ => cases e
  | hard _ => cases e

/-- The constraint step keeps the bindings. -/
theorem constraintStep_ok (env : Env) (c : Option Constraint) (σ σ' : Bindings)
    (e : constraintStep env c σ = .ok σ') : σ' = σ := by
  cases c with
  | none => simp only [constraintStep, Subst.ok.injEq] at e; exact e.symm
  | some c =>
    simp only [constraintStep, Subst.bind_eq] at e
    cases hs : Constraint.satisfied env.atomic σ c with
    | ok b =>
      rw [hs] at e
      cases b
      · cases e
      · simp only [Subst.bind_ok, ↓reduceIte, Subst.pure_eq, Subst.ok.injEq] at e; exact e.symm
    | soft _ => rw [hs] at e; cases e
    | hard _ => rw [hs] at e; cases e

/-- The non-dependent step keeps the bindings. -/
theorem nonDependentStep_ok (env : Env) (ps : List Ty) (args : List CallArg) (σ σ' : Bindings)
    (h : nonDependentStep env ps args σ = .ok σ') : σ' = σ := by
  simp only [nonDependentStep] at h
  induction ps generalizing args with
  | nil => cases args <;> (simp only [nonDependentStep.go, Subst.ok.injEq] at h; exact h.symm)
  | cons p ps ih =>
    cases args with
    | nil => simp only [nonDependentStep.go, Subst.ok.injEq] at h; exact h.symm
    | cons a as =>
      simp only [nonDependentStep.go] at h
      split at h
      · exact ih as h
      · cases hc : env.convertible a p with
        | ok b =>
          rw [hc] at h
          cases b
          · cases h
          · exact ih as h
        | soft _ => rw [hc] at h; cases h
        | hard _ => rw [hc] at h; cases h

/-- The specialization the function type step forms carries the bindings
as its template arguments. -/
theorem functionTypeStep_args (env : Env) (ft : FunctionTemplate) (σ : Bindings) (s : Specialization)
    (e : functionTypeStep env ft σ = .ok s) : s.args = σ := by
  simp only [functionTypeStep, Subst.bind_eq] at e
  cases hp : formAll env (ft.params.map (Ty.subst σ)) with
  | ok _ =>
    rw [hp] at e
    simp only [Subst.bind_ok] at e
    cases hr : form env (ft.ret.subst σ) with
    | ok _ => rw [hr] at e; simp only [Subst.bind_ok, Subst.pure_eq, Subst.ok.injEq] at e; rw [← e]
    | soft _ => rw [hr] at e; cases e
    | hard _ => rw [hr] at e; cases e
  | soft _ => rw [hp] at e; cases e
  | hard _ => rw [hp] at e; cases e

end Overload
