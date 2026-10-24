-- Overload/Constraint.lean                                           -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Syntax
import Overload.Outcome
import Overload.Types

/-!
# Constraints

Satisfaction, atomic identity, normal forms and subsumption. The step
order of [temp.deduct.general]/5 needs satisfaction: whether the
associated constraints of a function template hold for the deduced
arguments. Partial ordering needs subsumption. An atomic constraint is an
expression the model does not look inside, so the environment answers it
as an oracle, after the parameter mapping has been substituted.

The phase 3 theorems: subsumption is propositional implication with
atomic constraints as free variables (`subsumes_iff`), so it is a
preorder (`subsumes_refl`, `subsumes_trans`) but not antisymmetric
(`subsumes_not_antisymm`); it implies satisfaction-implication up to hard
errors (`subsumes_satisfied`, `subsumes_satisfied_hard`); and the
converse fails (`satisfaction_implication_not_subsumes`).
-/

namespace Overload

/-- A requirement of a requires-expression, on the fragment: a
simple-requirement asserting the validity of a call, by callee and
argument types, where an lvalue reference type is an lvalue argument and
any other type an xvalue, as `declval` gives; a call on an object of a
class; and a type-requirement asserting the validity of a type. The
requirement-parameter-list is notation ([expr.prim.req.general]/4), and
the model writes the arguments' types directly. Compound and nested
requirements are a later stage. -/
inductive Constraint.Requirement where
  | simple (callee : String) (args : List Ty)
  | memberCall (cls : Ty) (callee : String) (args : List Ty)
  | type (t : Ty)
  deriving Repr, DecidableEq, Inhabited

attribute [std rule "expr.prim.req.simple#1"] Constraint.Requirement.simple Constraint.Requirement.memberCall
attribute [std rule "expr.prim.req.type#1"] Constraint.Requirement.type

/-- Substitute bindings into a requirement's types. -/
def Constraint.Requirement.subst (σ : Bindings) : Constraint.Requirement → Constraint.Requirement
  | .simple f as => .simple f (as.map (Ty.subst σ))
  | .memberCall c f as => .memberCall (Ty.subst σ c) f (as.map (Ty.subst σ))
  | .type t => .type (Ty.subst σ t)

/-- A constraint: atomic constraints joined by conjunction and
disjunction, and the forms normalization expands or keeps. An atomic
constraint is an expression, named, with its parameter mapping; a type
trait the program answers, with its mapping; a requires-expression, an
atomic constraint of its own ([temp.constr.normal]/1), with a mapping
the environment may ignore; or a concept-id, which normalization
replaces by the concept's constraint with the arguments substituted. -/
inductive Constraint where
  | atomic (expr : String) (mapping : List Ty)
  | trait (q : Trait) (mapping : List Ty)
  | requires (reqs : List Constraint.Requirement) (mapping : List Ty)
  | conceptId (name : String) (args : List Ty)
  | conj (left right : Constraint)
  | disj (left right : Constraint)
  deriving Repr, DecidableEq, Inhabited

attribute [std rule "temp.constr.normal#1"] Constraint.requires Constraint.conceptId

namespace Constraint

/-- The head of an atomic constraint: an expression, identified by its
name; a trait query; a requires-expression, its requirements with the
bindings substituted; or a concept-id normalization did not expand,
which no program declares. -/
inductive Atom where
  | expr (e : String)
  | trait (q : Trait)
  | requires (reqs : List Constraint.Requirement)
  | concept (name : String)
  deriving Repr, DecidableEq, Inhabited

/-- Substitute bindings into a head: only a requires-expression carries
types. -/
def Atom.subst (σ : Bindings) : Atom → Atom
  | .requires reqs => .requires (reqs.map (Requirement.subst σ))
  | a => a

/-- The oracle for an atomic constraint: given its head, an expression or
a trait, and the substituted targets of its mapping, whether it is valid
and `true`. A `soft` answer is an invalid substitution in the immediate
context. The environment a program defines answers a trait from the
program (`Program.trait`) and an expression from what it knows. -/
abbrev Oracle := Atom → List Ty → Subst Bool

/-- An oracle for expressions alone, by name. -/
abbrev ExprOracle := String → List Ty → Subst Bool

/-- The oracle that answers expressions by `f` and traits by their
structural answer, `Trait.answer`, which needs no program. -/
def Oracle.ofExpr (f : ExprOracle) : Oracle
  | .expr e, m => f e m
  | .trait q, m => Trait.answer q m
  | .requires _, _ => .soft "a requires-expression needs the program"
  | .concept n, _ => .hard s!"the concept {n} is not declared"

/-- Satisfaction. For an atomic constraint the mapping is substituted into
the expression, an invalid result in the immediate context means not
satisfied, and otherwise the expression's value decides. Conjunction checks
its right operand only when the left is satisfied, and disjunction only
when the left is not. -/
@[std rule "temp.constr.atomic#3.sentence-1"]
def satisfied (oracle : Oracle) (σ : Bindings) : Constraint → Subst Bool
  | atomic e m =>
    match oracle (.expr e) (m.map (Ty.subst σ)) with
    | .soft _ => .ok false
    | r => r
  | trait q m =>
    match oracle (.trait q) (m.map (Ty.subst σ)) with
    | .soft _ => .ok false
    | r => r
  | requires reqs m =>
    match oracle (.requires (reqs.map (Requirement.subst σ))) (m.map (Ty.subst σ)) with
    | .soft _ => .ok false
    | r => r
  | conceptId n as =>
    match oracle (.concept n) (as.map (Ty.subst σ)) with
    | .soft _ => .ok false
    | r => r
  | conj l r => do
    if ← satisfied oracle σ l then satisfied oracle σ r else pure false
  | disj l r => do
    if ← satisfied oracle σ l then pure true else satisfied oracle σ r

/-- An invalid substitution in an atomic constraint's immediate context is
"not satisfied", never a deduction failure of its own. -/
@[std rule "temp.constr.atomic#3.sentence-2"]
theorem satisfied_atomic_soft (oracle : Oracle) (σ : Bindings) (e : String) (m : List Ty)
    (r : Reason) (h : oracle (.expr e) (m.map (Ty.subst σ)) = .soft r) :
    satisfied oracle σ (atomic e m) = .ok false := by
  simp [satisfied, h]

/-- How satisfaction reads an atomic constraint's answer: an invalid
expression is not satisfied, and anything else stands. -/
def atomicAnswer : Subst Bool → Subst Bool
  | .ok b => .ok b
  | .soft _ => .ok false
  | .hard r => .hard r

theorem satisfied_atomic (oracle : Oracle) (σ : Bindings) (e : String) (m : List Ty) :
    satisfied oracle σ (atomic e m) = atomicAnswer (oracle (.expr e) (m.map (Ty.subst σ))) := by
  simp only [satisfied]
  cases oracle (.expr e) (m.map (Ty.subst σ)) <;> rfl

/-! ## Subsumption -/

/-- An atomic constraint, as a clause element: its head and the targets
of its parameter mapping. -/
abbrev Atomic := Atom × List Ty

/-- The constraint of one atomic constraint. -/
def ofAtomic : Atomic → Constraint
  | (.expr e, m) => atomic e m
  | (.trait q, m) => trait q m
  | (.requires reqs, m) => requires reqs m
  | (.concept n, m) => conceptId n m

/-- The answer of an atomic constraint under the oracle, once the
bindings are substituted into its head and its mapping. -/
def answer (oracle : Oracle) (σ : Bindings) (a : Atomic) : Subst Bool :=
  oracle (a.1.subst σ) (a.2.map (Ty.subst σ))

theorem satisfied_trait (oracle : Oracle) (σ : Bindings) (q : Trait) (m : List Ty) :
    satisfied oracle σ (trait q m) = atomicAnswer (oracle (.trait q) (m.map (Ty.subst σ))) := by
  simp only [satisfied]
  cases oracle (.trait q) (m.map (Ty.subst σ)) <;> rfl

theorem satisfied_requires (oracle : Oracle) (σ : Bindings) (reqs : List Requirement) (m : List Ty) :
    satisfied oracle σ (requires reqs m) =
      atomicAnswer (oracle (.requires (reqs.map (Requirement.subst σ))) (m.map (Ty.subst σ))) := by
  simp only [satisfied]
  cases oracle (.requires (reqs.map (Requirement.subst σ))) (m.map (Ty.subst σ)) <;> rfl

theorem satisfied_conceptId (oracle : Oracle) (σ : Bindings) (n : String) (as : List Ty) :
    satisfied oracle σ (conceptId n as) = atomicAnswer (oracle (.concept n) (as.map (Ty.subst σ))) := by
  simp only [satisfied]
  cases oracle (.concept n) (as.map (Ty.subst σ)) <;> rfl

theorem satisfied_ofAtomic (oracle : Oracle) (σ : Bindings) (a : Atomic) :
    satisfied oracle σ (ofAtomic a) = atomicAnswer (answer oracle σ a) := by
  obtain ⟨h, m⟩ := a
  cases h with
  | expr e => exact satisfied_atomic oracle σ e m
  | trait q => exact satisfied_trait oracle σ q m
  | requires reqs => exact satisfied_requires oracle σ reqs m
  | concept n => exact satisfied_conceptId oracle σ n m


/-- Two atomic constraints are identical when they are formed from the
same appearance of the same expression and their parameter mappings
have the same targets. The fragment has no concept-ids to expand, so an
expression is identified by its name, and the targets compare as
template-ids do: structurally. -/
@[std rule "temp.constr.atomic#2.sentence-1"]
def identical (a b : Atomic) : Bool := a == b

/-- The disjunctive normal form: a disjunction of clauses, each a
conjunction of atomic constraints. -/
@[std rule "temp.constr.order#1"]
def dnf : Constraint → List (List Atomic)
  | atomic e m => [[(.expr e, m)]]
  | trait q m => [[(.trait q, m)]]
  | requires reqs m => [[(.requires reqs, m)]]
  | conceptId n as => [[(.concept n, as)]]
  | disj l r => dnf l ++ dnf r
  | conj l r => (dnf l).flatMap fun p => (dnf r).map fun q => p ++ q

/-- The conjunctive normal form: a conjunction of clauses, each a
disjunction of atomic constraints. -/
@[std rule "temp.constr.order#1"]
def cnf : Constraint → List (List Atomic)
  | atomic e m => [[(.expr e, m)]]
  | trait q m => [[(.trait q, m)]]
  | requires reqs m => [[(.requires reqs, m)]]
  | conceptId n as => [[(.concept n, as)]]
  | conj l r => cnf l ++ cnf r
  | disj l r => (cnf l).flatMap fun p => (cnf r).map fun q => p ++ q

theorem dnf_ofAtomic (a : Atomic) : dnf (ofAtomic a) = [[a]] := by
  obtain ⟨h, m⟩ := a; cases h <;> rfl

theorem cnf_ofAtomic (a : Atomic) : cnf (ofAtomic a) = [[a]] := by
  obtain ⟨h, m⟩ := a; cases h <;> rfl

/-- `P` subsumes `Q` if and only if every disjunctive clause of `P`'s
disjunctive normal form subsumes every conjunctive clause of `Q`'s
conjunctive normal form, where a disjunctive clause subsumes a
conjunctive clause when some atomic constraint of the first is identical
to some atomic constraint of the second. -/
@[std rule "temp.constr.order#1.sentence-1"]
def subsumes (p q : Constraint) : Bool :=
  (dnf p).all fun pi => (cnf q).all fun qj =>
    pi.any fun a => qj.any fun b => identical a b

/-- `D1` is at least as constrained as `D2` if both are constrained and
`D1`'s constraints subsume `D2`'s, or `D2` has none. Every constraint of
the fragment is eligible for subsumption. -/
@[std rule "temp.constr.order#4"]
def atLeastAsConstrained : Option Constraint → Option Constraint → Bool
  | _, none => true
  | some p, some q => subsumes p q
  | none, some _ => false

/-- `D1` is more constrained than `D2`: at least as constrained, and not
the other way round. -/
@[std rule "temp.constr.order#5"]
def moreConstrained (c₁ c₂ : Option Constraint) : Bool :=
  atLeastAsConstrained c₁ c₂ && !atLeastAsConstrained c₂ c₁

/-- Nothing is more constrained than itself. -/
theorem moreConstrained_irrefl (c : Option Constraint) : moreConstrained c c = false := by
  simp [moreConstrained]

/-- More constrained is asymmetric. -/
theorem moreConstrained_asymm (c₁ c₂ : Option Constraint) (h : moreConstrained c₁ c₂ = true) :
    moreConstrained c₂ c₁ = false := by
  simp only [moreConstrained, Bool.and_eq_true, Bool.not_eq_true'] at h
  simp [moreConstrained, h.1, h.2]

/-! ## Subsumption as implication

With atomic constraints read as free propositional variables, subsumption
is exactly propositional implication (`subsumes_iff`), because a
conjunction of atomic constraints implies a disjunction of them only when
they share one. That gives the preorder at once, and the link to
satisfaction: an assignment that comes from the oracle is one such
reading. -/

/-- The value of a constraint when each atomic constraint is given a truth
value. -/
def eval (v : Atomic → Bool) : Constraint → Bool
  | atomic e m => v (.expr e, m)
  | trait q m => v (.trait q, m)
  | requires reqs m => v (.requires reqs, m)
  | conceptId n as => v (.concept n, as)
  | conj l r => eval v l && eval v r
  | disj l r => eval v l || eval v r

theorem eval_iff_dnf (v : Atomic → Bool) (c : Constraint) :
    eval v c = true ↔ ∃ pi ∈ dnf c, ∀ a ∈ pi, v a = true := by
  induction c with
  | atomic e m => simp [eval, dnf]
  | trait q m => simp [eval, dnf]
  | requires reqs m => simp [eval, dnf]
  | conceptId n as => simp [eval, dnf]
  | disj l r ihl ihr =>
    simp only [eval, dnf, Bool.or_eq_true, ihl, ihr, List.mem_append]
    constructor
    · rintro (⟨pi, h, ha⟩ | ⟨pi, h, ha⟩)
      · exact ⟨pi, .inl h, ha⟩
      · exact ⟨pi, .inr h, ha⟩
    · rintro ⟨pi, h | h, ha⟩
      · exact .inl ⟨pi, h, ha⟩
      · exact .inr ⟨pi, h, ha⟩
  | conj l r ihl ihr =>
    simp only [eval, dnf, Bool.and_eq_true, ihl, ihr, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨⟨p, hp, hpa⟩, ⟨q, hq, hqa⟩⟩
      refine ⟨p ++ q, ⟨p, hp, q, hq, rfl⟩, fun a ha => ?_⟩
      rcases List.mem_append.1 ha with h | h
      · exact hpa a h
      · exact hqa a h
    · rintro ⟨_, ⟨p, hp, q, hq, rfl⟩, ha⟩
      exact ⟨⟨p, hp, fun a h => ha a (List.mem_append_left _ h)⟩,
        ⟨q, hq, fun a h => ha a (List.mem_append_right _ h)⟩⟩

theorem eval_iff_cnf (v : Atomic → Bool) (c : Constraint) :
    eval v c = true ↔ ∀ qj ∈ cnf c, ∃ a ∈ qj, v a = true := by
  induction c with
  | atomic e m =>
    simp only [eval, cnf, List.mem_singleton, forall_eq, Prod.exists, Prod.mk.injEq]
    constructor
    · exact fun h => ⟨.expr e, m, ⟨rfl, rfl⟩, h⟩
    · rintro ⟨_, _, ⟨rfl, rfl⟩, h⟩
      exact h
  | trait q m =>
    simp only [eval, cnf, List.mem_singleton, forall_eq, Prod.exists, Prod.mk.injEq]
    constructor
    · exact fun h => ⟨.trait q, m, ⟨rfl, rfl⟩, h⟩
    · rintro ⟨_, _, ⟨rfl, rfl⟩, h⟩
      exact h
  | requires reqs m =>
    simp only [eval, cnf, List.mem_singleton, forall_eq, Prod.exists, Prod.mk.injEq]
    constructor
    · exact fun h => ⟨.requires reqs, m, ⟨rfl, rfl⟩, h⟩
    · rintro ⟨_, _, ⟨rfl, rfl⟩, h⟩
      exact h
  | conceptId n as =>
    simp only [eval, cnf, List.mem_singleton, forall_eq, Prod.exists, Prod.mk.injEq]
    constructor
    · exact fun h => ⟨.concept n, as, ⟨rfl, rfl⟩, h⟩
    · rintro ⟨_, _, ⟨rfl, rfl⟩, h⟩
      exact h
  | conj l r ihl ihr =>
    simp only [eval, cnf, Bool.and_eq_true, ihl, ihr, List.mem_append]
    constructor
    · rintro ⟨hl, hr⟩ qj (h | h)
      · exact hl qj h
      · exact hr qj h
    · intro h
      exact ⟨fun qj hq => h qj (.inl hq), fun qj hq => h qj (.inr hq)⟩
  | disj l r ihl ihr =>
    simp only [eval, cnf, Bool.or_eq_true, ihl, ihr, List.mem_flatMap, List.mem_map]
    constructor
    · rintro (h | h) _ ⟨p, hp, q, hq, rfl⟩
      · obtain ⟨a, ha, hv⟩ := h p hp
        exact ⟨a, List.mem_append_left _ ha, hv⟩
      · obtain ⟨a, ha, hv⟩ := h q hq
        exact ⟨a, List.mem_append_right _ ha, hv⟩
    · intro h
      apply Classical.byContradiction
      intro hn
      simp only [not_or, Classical.not_forall, not_exists, not_and] at hn
      obtain ⟨⟨p, hp, hpn⟩, ⟨q, hq, hqn⟩⟩ := hn
      obtain ⟨a, ha, hv⟩ := h (p ++ q) ⟨p, hp, q, hq, rfl⟩
      rcases List.mem_append.1 ha with h' | h'
      · exact absurd hv (by simp [hpn a h'])
      · exact absurd hv (by simp [hqn a h'])

/-- Subsumption is propositional implication, atomic constraints read as
free variables. -/
theorem subsumes_iff (p q : Constraint) :
    subsumes p q = true ↔ ∀ v, eval v p = true → eval v q = true := by
  simp only [subsumes, List.all_eq_true, List.any_eq_true, identical, beq_iff_eq]
  constructor
  · intro h v hp
    obtain ⟨pi, hpi, hv⟩ := (eval_iff_dnf v p).1 hp
    refine (eval_iff_cnf v q).2 fun qj hqj => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := h pi hpi qj hqj
    exact ⟨a, hb, hv a ha⟩
  · intro h pi hpi qj hqj
    -- The assignment that makes exactly the atomic constraints of `pi` true.
    have hq := h (fun a => decide (a ∈ pi)) ((eval_iff_dnf _ p).2 ⟨pi, hpi, fun a ha => by simp [ha]⟩)
    obtain ⟨b, hb, hv⟩ := (eval_iff_cnf _ q).1 hq qj hqj
    exact ⟨b, by simpa using hv, b, hb, rfl⟩

/-- Subsumption is reflexive. -/
theorem subsumes_refl (p : Constraint) : subsumes p p = true :=
  (subsumes_iff p p).2 fun _ h => h

/-- Subsumption is transitive. -/
theorem subsumes_trans {p q r : Constraint} (hpq : subsumes p q = true) (hqr : subsumes q r = true) :
    subsumes p r = true :=
  (subsumes_iff p r).2 fun v h => (subsumes_iff q r).1 hqr v ((subsumes_iff p q).1 hpq v h)

/-- At least as constrained is a preorder: reflexive. -/
theorem atLeastAsConstrained_refl (c : Option Constraint) : atLeastAsConstrained c c = true := by
  cases c <;> simp [atLeastAsConstrained, subsumes_refl]

/-- At least as constrained is a preorder: transitive. -/
theorem atLeastAsConstrained_trans {c₁ c₂ c₃ : Option Constraint}
    (h₁ : atLeastAsConstrained c₁ c₂ = true) (h₂ : atLeastAsConstrained c₂ c₃ = true) :
    atLeastAsConstrained c₁ c₃ = true := by
  cases c₃ with
  | none => rfl
  | some r =>
    cases c₂ with
    | none => simp [atLeastAsConstrained] at h₂
    | some q =>
      cases c₁ with
      | none => simp [atLeastAsConstrained] at h₁
      | some p => exact subsumes_trans h₁ h₂

/-- The example of [temp.constr.order]/1, for any two different atomic
constraints `A` and `B`: `A ∧ B` subsumes `A` but not the other way round,
`A` subsumes `A ∨ B` but not the other way round, and every constraint
subsumes itself. -/
@[std example "temp.constr.order#1"]
theorem subsumes_example (a b : Atomic) (hne : a ≠ b) :
    let A := ofAtomic a
    let B := ofAtomic b
    subsumes (conj A B) A = true ∧ subsumes A (conj A B) = false ∧
    subsumes A (disj A B) = true ∧ subsumes (disj A B) A = false ∧
    ∀ c, subsumes c c = true := by
  have hne' : b ≠ a := Ne.symm hne
  refine ⟨?_, ?_, ?_, ?_, subsumes_refl⟩ <;>
    simp_all [subsumes, dnf, cnf, dnf_ofAtomic, cnf_ofAtomic, identical]

/-- The note of [temp.constr.order]/2 calls subsumption a partial ordering.
It is a preorder, reflexive and transitive, but not antisymmetric: `A ∧ B`
and `B ∧ A` subsume each other and are different constraints. It is a
partial order only on constraints taken up to mutual subsumption. -/
@[std note "temp.constr.order#2.sentence-1"]
theorem subsumes_not_antisymm :
    (∀ p, subsumes p p = true) ∧
    (∀ p q r, subsumes p q = true → subsumes q r = true → subsumes p r = true) ∧
    ∃ p q, p ≠ q ∧ subsumes p q = true ∧ subsumes q p = true :=
  ⟨subsumes_refl, fun _ _ _ => subsumes_trans,
    conj (atomic "A" []) (atomic "B" []), conj (atomic "B" []) (atomic "A" []),
    by simp, rfl, rfl⟩

/-! ## Subsumption and satisfaction -/

/-- The truth value the oracle gives each atomic constraint under `σ`: true
when it is valid and true, false otherwise. -/
def oracleAssignment (oracle : Oracle) (σ : Bindings) (a : Atomic) : Bool :=
  answer oracle σ a == .ok true

/-- Satisfaction never fails softly: a substitution failure in an atomic
constraint is "not satisfied". -/
theorem satisfied_ne_soft (oracle : Oracle) (σ : Bindings) (c : Constraint) (r : Reason) :
    satisfied oracle σ c ≠ .soft r := by
  induction c generalizing r with
  | atomic e m | trait e m | requires e m | conceptId e m =>
    simp only [satisfied]
    split <;> simp_all
  | conj l _ ihl ihr | disj l _ ihl ihr =>
    simp only [satisfied, Subst.bind_eq]
    cases h : satisfied oracle σ l with
    | ok b => cases b <;> simp_all
    | soft r' => exact absurd h (ihl r')
    | hard _ => simp

/-- Where satisfaction succeeds, it computes the constraint's value under
the oracle's assignment; short-circuiting does not change the value. -/
theorem satisfied_ok_eval (oracle : Oracle) (σ : Bindings) (c : Constraint) (b : Bool)
    (h : satisfied oracle σ c = .ok b) : b = eval (oracleAssignment oracle σ) c := by
  induction c generalizing b with
  | atomic e m | trait e m | requires e m | conceptId e m =>
    simp only [satisfied] at h
    simp only [eval, oracleAssignment, answer, Atom.subst]
    split at h
    · next hs => simp_all
    · next r hs => rw [h]; cases b <;> simp_all
  | conj l r ihl ihr =>
    simp only [satisfied, Subst.bind_eq] at h
    cases hl : satisfied oracle σ l with
    | ok bl =>
      rw [hl] at h
      have := ihl bl hl
      cases bl
      · simp at h; subst h; simp [eval, ← this]
      · simp at h; simp [eval, ← this, ← ihr b h]
    | soft _ => rw [hl] at h; cases h
    | hard _ => rw [hl] at h; cases h
  | disj l r ihl ihr =>
    simp only [satisfied, Subst.bind_eq] at h
    cases hl : satisfied oracle σ l with
    | ok bl =>
      rw [hl] at h
      have := ihl bl hl
      cases bl
      · simp at h; simp [eval, ← this, ← ihr b h]
      · simp at h; subst h; simp [eval, ← this]
    | soft _ => rw [hl] at h; cases h
    | hard _ => rw [hl] at h; cases h

/-- Subsumption implies satisfaction-implication, up to hard errors: when
`P` subsumes `Q` and `P` is satisfied, `Q` is satisfied or checking it is a
hard error. The hard error is real: checking `Q` can reach an atomic
constraint that checking `P` never evaluated (`subsumes_satisfied_hard`). -/
theorem subsumes_satisfied (oracle : Oracle) (σ : Bindings) {p q : Constraint}
    (hs : subsumes p q = true) (hp : satisfied oracle σ p = .ok true) :
    satisfied oracle σ q = .ok true ∨ ∃ r, satisfied oracle σ q = .hard r := by
  have hq := (subsumes_iff p q).1 hs _ (satisfied_ok_eval oracle σ p true hp).symm
  cases h : satisfied oracle σ q with
  | ok b => exact .inl (by rw [satisfied_ok_eval oracle σ q b h, hq])
  | soft r => exact absurd h (satisfied_ne_soft oracle σ q r)
  | hard r => exact .inr ⟨r, rfl⟩

/-- The converse fails: satisfaction can imply satisfaction without
subsumption, since subsumption sees only the identity of atomic
constraints, not what they mean. Here two different atomic constraints
are always true. -/
theorem satisfaction_implication_not_subsumes :
    ∃ (oracle : Oracle) (p q : Constraint),
      (∀ σ, satisfied oracle σ p = .ok true → satisfied oracle σ q = .ok true) ∧
      subsumes p q = false :=
  ⟨fun _ _ => .ok true, atomic "A" [], atomic "B" [], fun _ _ => rfl, rfl⟩

/-- The hard error in `subsumes_satisfied` happens: `A` subsumes `B ∨ A`,
and checking `B ∨ A` evaluates `B` first, which `A` never did. -/
theorem subsumes_satisfied_hard :
    ∃ (oracle : Oracle) (p q : Constraint), subsumes p q = true ∧
      satisfied oracle [] p = .ok true ∧ ∃ r, satisfied oracle [] q = .hard r :=
  ⟨fun a _ => if a = .expr "A" then .ok true else .hard "B is ill-formed", atomic "A" [],
    disj (atomic "B" []) (atomic "A" []), rfl, rfl, _, rfl⟩

end Constraint

end Overload
