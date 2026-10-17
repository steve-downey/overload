-- Overload/Deduction.lean                                            -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Syntax
import Overload.Outcome

/-!
# Template argument deduction on the fragment

Deduction is given twice, per the `spec-style` decision: as a relation that
transcribes [temp.deduct.type], one constructor per sentence, and as a
function that is executable. `deduceTy_sound` and `deduceTy_complete` are
the agreement theorem; `deduceTy_det` is determinism, which the function
form makes immediate.

The relation is on one `P`/`A` pair and the bindings before and after it.
A list of pairs is a chain, and [temp.deduct.type]/2 sentence 3 is what
makes the chain legitimate: the pairs are deduced independently and the
values combined, and a conflict between pairs is a failure, which `bindArg`
enforces at the point of binding.

Then the call-site adjustments of [temp.deduct.call]/2 and /3, and
`deduceCall`, which deduces every parameter of a function template against
the arguments of a call.
-/

namespace Overload

/-- Record the argument deduced for parameter `i`, or fail if a different
argument was already deduced for it ([temp.deduct.type]/2 sentence 3). -/
def bindArg (i : ParamIdx) (a : Ty) (σ : Bindings) : Option Bindings :=
  match σ.lookup i with
  | some b => if b = a then some σ else none
  | none => some ((i, a) :: σ)

/-- Deduce a constant template argument. A value that mentions a template
parameter below the top is a non-deduced context ([temp.deduct.type]/5),
so it does not participate and is checked later by substitution. -/
def deduceVal (p a : Val) (σ : Bindings) : Option Bindings :=
  match p with
  | .param i => bindArg i (.value a) σ
  | p => if p.dependent then some σ else if p = a then some σ else none

/-- The executable form: deduce the template arguments that make `P`
identical to `A`, on top of the bindings so far. -/
def deduceTy : Ty → Ty → Bindings → Option Bindings
  | .param i, a, σ => if a.isType then bindArg i a σ else none
  | .value p, .value a, σ => deduceVal p a σ
  | .named n, .named m, σ => if n = m then some σ else none
  | .const p, .const a, σ => deduceTy p a σ
  | .ptr p, .ptr a, σ => deduceTy p a σ
  | .lref p, .lref a, σ => deduceTy p a σ
  | .rref p, .rref a, σ => deduceTy p a σ
  | .spec c ps, .spec d as, σ => if c = d then deduceTy ps as σ else none
  | .nil, .nil, σ => some σ
  | .cons p ps, .cons a as, σ => deduceTy p a σ >>= deduceTy ps as
  | .nondeduced _, _, σ => some σ
  | .lookup _ _, _, σ => some σ
  | .ref _, _, σ => some σ
  | .removeCvref _, _, σ => some σ
  | _, _, _ => none

/-- The specification form: `DeduceTy P A σ σ'` says that deducing `P`
against `A` on top of `σ` succeeds with `σ'`. Each constructor transcribes
one of the forms of [temp.deduct.type]/8, or one of the sentences around
them. The relation says nothing about failure: a pair with no derivation
is one on which deduction fails. -/
@[specification]
inductive DeduceTy : Ty → Ty → Bindings → Bindings → Prop where
  /-- The form `T`: a type template argument is deduced from the whole of
  `A`, consistently with what was deduced elsewhere. -/
  | param (i : ParamIdx) (a : Ty) (σ σ' : Bindings) :
      a.isType = true → bindArg i a σ = some σ' → DeduceTy (.param i) a σ σ'
  /-- The form `i` inside a template argument list: a constant template
  argument is deduced from the corresponding value. -/
  | value (p a : Val) (σ σ' : Bindings) :
      deduceVal p a σ = some σ' → DeduceTy (.value p) (.value a) σ σ'
  /-- A component that is the same non-dependent type in `P` and `A`. -/
  | named (n : String) (σ : Bindings) :
      DeduceTy (.named n) (.named n) σ σ
  /-- The form `cv T`. -/
  | const (p a : Ty) (σ σ' : Bindings) :
      DeduceTy p a σ σ' → DeduceTy (.const p) (.const a) σ σ'
  /-- The form `T*`. -/
  | ptr (p a : Ty) (σ σ' : Bindings) :
      DeduceTy p a σ σ' → DeduceTy (.ptr p) (.ptr a) σ σ'
  /-- The form `T&`. -/
  | lref (p a : Ty) (σ σ' : Bindings) :
      DeduceTy p a σ σ' → DeduceTy (.lref p) (.lref a) σ σ'
  /-- The form `T&&`. -/
  | rref (p a : Ty) (σ σ' : Bindings) :
      DeduceTy p a σ σ' → DeduceTy (.rref p) (.rref a) σ σ'
  /-- The forms `TT<T>` and `TT<i>`, for a class template `TT`: the
  specialization's argument list is compared argument by argument. -/
  | spec (c : String) (ps as : Ty) (σ σ' : Bindings) :
      DeduceTy ps as σ σ' → DeduceTy (.spec c ps) (.spec c as) σ σ'
  /-- The end of two argument lists of the same length. -/
  | nil (σ : Bindings) :
      DeduceTy .nil .nil σ σ
  /-- Each argument `Pᵢ` is compared with the corresponding `Aᵢ`, and the
  deduced values are combined. -/
  | cons (p ps a as : Ty) (σ σ₁ σ' : Bindings) :
      DeduceTy p a σ σ₁ → DeduceTy ps as σ₁ σ' → DeduceTy (.cons p ps) (.cons a as) σ σ'
  /-- A non-deduced context: the value does not participate in deduction,
  and takes what was deduced elsewhere or explicitly specified. -/
  | nondeduced (p a : Ty) (σ : Bindings) :
      DeduceTy (.nondeduced p) a σ σ
  /-- A constant template argument in which a subexpression references a
  template parameter is a non-deduced context: the lookup's argument is
  not deduced from, whatever `A` is. -/
  | lookup (n : String) (p a : Ty) (σ : Bindings) :
      DeduceTy (.lookup n p) a σ σ
  /-- So is a reference constant template argument whose operand
  references a template parameter, such as `functor<T>`; one whose operand
  does not is the same object or no match, which the fragment's uses never
  ask, since the instance parameter is always defaulted. -/
  | ref (p a : Ty) (σ : Bindings) :
      DeduceTy (.ref p) a σ σ
  /-- `std::remove_cvref_t<T>` names `std::remove_cvref<T>::type`: the
  nested-name-specifier of a qualified-id is a non-deduced context. -/
  | removeCvref (p a : Ty) (σ : Bindings) :
      DeduceTy (.removeCvref p) a σ σ

attribute [std rule "temp.deduct.type#8.sentence-1"] DeduceTy.param
attribute [std rule "temp.deduct.type#8.sentence-1"] DeduceTy.value
attribute [std rule "temp.deduct.type#8.sentence-2"] DeduceTy.named
attribute [std rule "temp.deduct.type#8.sentence-1"] DeduceTy.const
attribute [std rule "temp.deduct.type#8.sentence-1"] DeduceTy.ptr
attribute [std rule "temp.deduct.type#8.sentence-1"] DeduceTy.lref
attribute [std rule "temp.deduct.type#8.sentence-1"] DeduceTy.rref
attribute [std rule "temp.deduct.type#9.sentence-1"] DeduceTy.spec
attribute [std rule "temp.deduct.type#9.sentence-1"] DeduceTy.nil
attribute [std rule "temp.deduct.type#9.sentence-1"] DeduceTy.cons
attribute [std rule "temp.deduct.type#4.sentence-3"] DeduceTy.nondeduced
attribute [std rule "temp.deduct.type#5"] DeduceTy.lookup
attribute [std rule "temp.deduct.type#5"] DeduceTy.ref
attribute [std rule "temp.deduct.type#5"] DeduceTy.removeCvref

/-- Soundness: what the function deduces, the relation derives. -/
theorem deduceTy_sound (p : Ty) : ∀ (a : Ty) (σ σ' : Bindings),
    deduceTy p a σ = some σ' → DeduceTy p a σ σ' := by
  induction p with
  | param i =>
    intro a σ σ' h
    simp only [deduceTy] at h
    split at h
    · exact .param i a σ σ' (by assumption) h
    · exact absurd h (by simp)
  | value p =>
    intro a σ σ' h
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    exact .value _ _ _ _ h
  | named n =>
    intro a σ σ' h
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact (by assumption : n = _) ▸ .named n σ
    · exact absurd h (by simp)
  | const p ih =>
    intro a σ σ' h
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    exact .const _ _ _ _ (ih _ _ _ h)
  | ptr p ih =>
    intro a σ σ' h
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    exact .ptr _ _ _ _ (ih _ _ _ h)
  | lref p ih =>
    intro a σ σ' h
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    exact .lref _ _ _ _ (ih _ _ _ h)
  | rref p ih =>
    intro a σ σ' h
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    exact .rref _ _ _ _ (ih _ _ _ h)
  | spec c ps ih =>
    intro a σ σ' h
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    split at h
    · exact (by assumption : c = _) ▸ .spec _ _ _ _ _ (ih _ _ _ h)
    · exact absurd h (by simp)
  | nil =>
    intro a σ σ' h
    cases a <;> simp only [deduceTy, reduceCtorEq, Option.some.injEq] at h
    subst h
    exact .nil σ
  | cons p ps ihp ihps =>
    intro a σ σ' h
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    rename_i a as
    obtain ⟨σ₁, h₁, h₂⟩ : ∃ σ₁, deduceTy p a σ = some σ₁ ∧ deduceTy ps as σ₁ = some σ' := by
      cases hd : deduceTy p a σ with
      | none => rw [hd] at h; cases h
      | some σ₁ => rw [hd] at h; exact ⟨σ₁, rfl, h⟩
    exact .cons _ _ _ _ _ _ _ (ihp _ _ _ h₁) (ihps _ _ _ h₂)
  | nondeduced p _ =>
    intro a σ σ' h
    simp only [deduceTy, Option.some.injEq] at h
    subst h
    exact .nondeduced p a σ
  | lookup n p _ =>
    intro a σ σ' h
    simp only [deduceTy, Option.some.injEq] at h
    subst h
    exact .lookup n p a σ
  | ref p _ =>
    intro a σ σ' h
    simp only [deduceTy, Option.some.injEq] at h
    subst h
    exact .ref p a σ
  | removeCvref p _ =>
    intro a σ σ' h
    simp only [deduceTy, Option.some.injEq] at h
    subst h
    exact .removeCvref p a σ

/-- Completeness: what the relation derives, the function deduces. -/
theorem deduceTy_complete {p a : Ty} {σ σ' : Bindings}
    (h : DeduceTy p a σ σ') : deduceTy p a σ = some σ' := by
  induction h with
  | param i a σ σ' ht hb => simp [deduceTy, ht, hb]
  | value p a σ σ' hv => simp [deduceTy, hv]
  | named n σ => simp [deduceTy]
  | const p a σ σ' _ ih => simp [deduceTy, ih]
  | ptr p a σ σ' _ ih => simp [deduceTy, ih]
  | lref p a σ σ' _ ih => simp [deduceTy, ih]
  | rref p a σ σ' _ ih => simp [deduceTy, ih]
  | spec c ps as σ σ' _ ih => simp [deduceTy, ih]
  | nil σ => simp [deduceTy]
  | cons p ps a as σ σ₁ σ' _ _ ih₁ ih₂ => simp [deduceTy, ih₁, ih₂]
  | nondeduced p a σ => simp [deduceTy]
  | lookup n p a σ => simp [deduceTy]
  | ref p a σ => simp [deduceTy]
  | removeCvref p a σ => simp [deduceTy]

/-- Agreement: the relation holds exactly when the function succeeds. -/
theorem deduceTy_iff (p a : Ty) (σ σ' : Bindings) :
    DeduceTy p a σ σ' ↔ deduceTy p a σ = some σ' :=
  ⟨deduceTy_complete, deduceTy_sound p a σ σ'⟩

/-- Determinism: one `P`/`A` pair and one starting point deduce at most one
set of values. The Standard makes "more than one possible set of deduced
values" a failure ([temp.deduct.type]/2); on this fragment it does not
arise. -/
@[std theorem "temp.deduct.type#2.sentence-3"]
theorem deduceTy_det {p a : Ty} {σ σ₁ σ₂ : Bindings}
    (h₁ : DeduceTy p a σ σ₁) (h₂ : DeduceTy p a σ σ₂) : σ₁ = σ₂ := by
  have e₁ := deduceTy_complete h₁
  have e₂ := deduceTy_complete h₂
  rw [e₁] at e₂
  exact Option.some.inj e₂

/-- Deduction only adds bindings: nothing deduced earlier is lost. -/
theorem deduceTy_extends (p : Ty) : ∀ (a : Ty) (σ σ' : Bindings),
    deduceTy p a σ = some σ' → ∀ b ∈ σ, b ∈ σ' := by
  induction p with
  | param i =>
    intro a σ σ' h b hb
    simp only [deduceTy] at h
    split at h
    · unfold bindArg at h
      split at h
      · split at h
        · simp only [Option.some.injEq] at h; subst h; exact hb
        · exact absurd h (by simp)
      · simp only [Option.some.injEq] at h; subst h; exact List.mem_cons_of_mem _ hb
    · exact absurd h (by simp)
  | value p =>
    intro a σ σ' h b hb
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    unfold deduceVal at h
    split at h
    · unfold bindArg at h
      split at h
      · split at h
        · simp only [Option.some.injEq] at h; subst h; exact hb
        · exact absurd h (by simp)
      · simp only [Option.some.injEq] at h; subst h; exact List.mem_cons_of_mem _ hb
    · split at h
      · simp only [Option.some.injEq] at h; subst h; exact hb
      · split at h
        · simp only [Option.some.injEq] at h; subst h; exact hb
        · exact absurd h (by simp)
  | named n =>
    intro a σ σ' h b hb
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact hb
    · exact absurd h (by simp)
  | const p ih | ptr p ih | lref p ih | rref p ih =>
    intro a σ σ' h b hb
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    exact ih _ _ _ h b hb
  | spec c ps ih =>
    intro a σ σ' h b hb
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    split at h
    · exact ih _ _ _ h b hb
    · exact absurd h (by simp)
  | nil =>
    intro a σ σ' h b hb
    cases a <;> simp only [deduceTy, reduceCtorEq, Option.some.injEq] at h
    subst h; exact hb
  | cons p ps ihp ihps =>
    intro a σ σ' h b hb
    cases a <;> simp only [deduceTy, reduceCtorEq] at h
    rename_i a as
    obtain ⟨σ₁, h₁, h₂⟩ : ∃ σ₁, deduceTy p a σ = some σ₁ ∧ deduceTy ps as σ₁ = some σ' := by
      cases hd : deduceTy p a σ with
      | none => rw [hd] at h; cases h
      | some σ₁ => rw [hd] at h; exact ⟨σ₁, rfl, h⟩
    exact ihps _ _ _ h₂ b (ihp _ _ _ h₁ b hb)
  | nondeduced p _ =>
    intro a σ σ' h b hb
    simp only [deduceTy, Option.some.injEq] at h
    subst h; exact hb
  | lookup n p _ =>
    intro a σ σ' h b hb
    simp only [deduceTy, Option.some.injEq] at h
    subst h; exact hb
  | ref p _ | removeCvref p _ =>
    intro a σ σ' h b hb
    simp only [deduceTy, Option.some.injEq] at h
    subst h; exact hb

/-! ## Deduction from a function call -/

/-- An argument of a call: its type, and whether it is an lvalue, which is
what a forwarding reference looks at. -/
structure CallArg where
  ty : Ty
  lvalue : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Is `P` a forwarding reference: an rvalue reference to a cv-unqualified
template parameter? -/
@[std rule "temp.deduct.call#3.sentence-3"]
def isForwardingRef : Ty → Bool
  | .rref (.param _) => true
  | _ => false

/-- The `A` used for deduction against `P`, after the adjustments of
[temp.deduct.call]/2 and /3: top-level cv-qualifiers of `A` are ignored
when `P` is not a reference, and an lvalue argument against a forwarding
reference deduces as an lvalue reference. Array and function types are
outside the fragment. -/
@[std rule "temp.deduct.call#2"]
def adjustA (p : Ty) (a : CallArg) : Ty :=
  if isForwardingRef p && a.lvalue then .lref a.ty
  else if p.isRef then a.ty
  else a.ty.stripConst

/-- The `P` used for deduction: top-level cv-qualifiers are ignored, and a
reference deduces by its referred type, which keeps its qualifiers. -/
@[std rule "temp.deduct.call#3.sentence-1"]
def adjustP (p : Ty) : Ty :=
  if p.isRef then p.referred else p.stripConst

/-- Deduce from one function parameter and its argument. A parameter whose
type does not participate in deduction (it is non-dependent) contributes
nothing here; overload resolution checks it.

When `P` is a reference, the deduced `A` may be more cv-qualified than the
transformed `A` ([temp.deduct.call]/4), and that alternative is considered
only if deduction would otherwise fail ([temp.deduct.call]/5): `const T&`
against an `int` prvalue deduces `T` as `int` on the second attempt. -/
@[std rule "temp.deduct.call#5.sentence-1"]
def deduceParam (p : Ty) (a : CallArg) (σ : Bindings) : Option Bindings :=
  if !p.dependent then some σ
  else
    let p' := adjustP p
    let a' := adjustA p a
    match deduceTy p' a' σ with
    | some σ' => some σ'
    | none => if p.isRef then deduceTy p'.stripConst a'.stripConst σ else none

/-- Deduce every parameter of a call, left to right. A parameter for which
the call has no argument, one whose default argument is being used, is a
non-deduced context ([temp.deduct.type]/5) and contributes nothing; a call
with more arguments than parameters is not a deduction failure but a
non-viable candidate, and here it fails, since nothing can be deduced for
it. -/
@[std rule "temp.deduct.call#1.sentence-1"]
def deduceCall : List Ty → List CallArg → Bindings → Option Bindings
  | _, [], σ => some σ
  | p :: ps, a :: as, σ => deduceParam p a σ >>= deduceCall ps as
  | [], _ :: _, _ => none

/-- After the call, every template parameter of the head must have a value:
one used only in non-deduced contexts, and not explicitly specified, fails
deduction. -/
@[std rule "temp.deduct.type#4.sentence-4"]
def allDeduced (arity : Nat) (σ : Bindings) : Bool :=
  (List.range arity).all fun i => (σ.lookup i).isSome

end Overload
