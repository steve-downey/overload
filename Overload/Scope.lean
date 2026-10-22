-- Overload/Scope.lean                                                -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Transitivity
import Overload.Mandates

/-!
# Correspondence: which declarations are one entity

Two declarations of a name are either one entity declared twice or two
entities that share a name, and overload resolution sees entities, not
declarations. [basic.scope.scope]/4 decides which: declarations
*correspond* when they introduce the same name, unless one declares a
type and the other a variable or function, or each declares a function or
function template and the two are not *corresponding overloads*, that is,
functions with the same parameter-type-list, or function templates with
equivalent template-heads, parameter lists and return types. Two
corresponding declarations in one scope that declare different kinds of
entity *potentially conflict*, and a program with such a pair is
ill-formed ([basic.scope.scope]/6, [basic.link]/11).

This module transcribes the rule as relation and function
(`Corresponds`, `corresponds`, `corresponds_iff`), the conflict check
(`potentiallyConflict`, `Program.conflicts`, `Program.scopesWellFormed`),
and the overload set a name's declarations form ([basic.lookup.general]/1):
one declaration per entity, the first, since a later corresponding
declaration is a redeclaration (`entities`, `Program.overloadSet`).

The theorem is `redeclaration_inert`: declaring a function or function
template again changes no call, because the overload set is unchanged.
`Program.candidates` lists declarations, so before this module a
redeclaration was two candidates with the same signature, and
`bestViable` reported an ambiguity between a function and itself
(`candidates_redeclaration_ambiguous`). Lookup, when it arrives, computes
the declarations found; the overload set is what resolution reads.
-/

namespace Overload

open PartialOrdering

/-! ## What a declaration declares -/

/-- The kind of entity a declaration declares, as [basic.link]/11
distinguishes them: two declarations of one entity must agree on it. -/
inductive EntityKind where
  | type
  | classTemplate
  | function
  | functionTemplate
  | variable
  | variableTemplate
  | concept
  deriving Repr, DecidableEq, Inhabited

/-- The name a declaration binds in its scope ([basic.scope.scope]/2), if
any. A partial specialization binds no name, and a use is not a
declaration. -/
def Decl.name? : Decl → Option String
  | .class n _ _ _ => some n
  | .classTemplate n _ _ => some n
  | .function n _ _ => some n
  | .functionTemplate ft => some ft.name
  | .lookup n | .lookupHard n => some n
  | .object n _ _ => some n
  | .concept n _ => some n
  | .instance .. | .use .. | .dependentCall .. | .refersTo _ => none

/-- The kind of entity a declaration declares, if it declares one. -/
def Decl.kind? : Decl → Option EntityKind
  | .class .. => some .type
  | .classTemplate .. => some .classTemplate
  | .function .. => some .function
  | .functionTemplate _ => some .functionTemplate
  | .lookup _ | .lookupHard _ => some .variableTemplate
  | .object .. => some .variable
  | .concept .. => some .concept
  | .instance .. | .use .. | .dependentCall .. | .refersTo _ => none

/-- The scope a declaration inhabits, its target scope in the fragment
([basic.scope.scope]/2). A partial specialization, a use, a variable
template and a concept are at global scope until lookup needs them
elsewhere. -/
def Decl.scope : Decl → Scope
  | .class _ _ _ s | .classTemplate _ _ s | .function _ _ s | .object _ _ s
  | .dependentCall _ _ s => s
  | .functionTemplate ft => ft.scope
  | _ => []

/-- Declares a type, and not a type alias: a class. A class template
declares a template. -/
def Decl.declaresType (d : Decl) : Bool := d.kind? == some .type

/-- Declares a variable, a function or a function template: the kinds a
type does not correspond with. -/
def Decl.declaresNonType (d : Decl) : Bool :=
  match d.kind? with
  | some .variable | some .function | some .functionTemplate => true
  | _ => false

/-- Declares a function or a function template. -/
def Decl.declaresFunction (d : Decl) : Bool :=
  match d.kind? with
  | some .function | some .functionTemplate => true
  | _ => false

/-! ## Correspondence -/

/-- Corresponding overloads: two functions with the same
parameter-type-list, or two function templates with corresponding
signatures (equivalent template parameters, parameter lists and return
types) and equivalent template-heads and trailing requires-clauses. The
fragment has no object parameters, so the object-parameter bullets are
vacuous, and a non-template function has no trailing requires-clause.
Equivalence of template parameters is [temp.over.link]/6, as the
tie-break gate reads it. -/
@[std rule "basic.scope.scope#4"]
def correspondingOverloads : Decl → Decl → Bool
  | .function _ ps _, .function _ qs _ => ps == qs
  | .functionTemplate f, .functionTemplate g =>
    headsEquivalent f.head g.head && f.params == g.params && f.ret == g.ret &&
      f.constraint == g.constraint
  | _, _ => false

/-- Two declarations correspond: they introduce the same name, unless one
declares a type and the other a variable, function or function template,
or each declares a function or function template and they do not declare
corresponding overloads. Using-declarators, constructors and destructors
are out of the fragment. -/
@[std rule "basic.scope.scope#4"]
def corresponds (d₁ d₂ : Decl) : Bool :=
  match d₁.name?, d₂.name? with
  | some n, some m =>
    n == m &&
    !(d₁.declaresType && d₂.declaresNonType) && !(d₂.declaresType && d₁.declaresNonType) &&
    (!(d₁.declaresFunction && d₂.declaresFunction) || correspondingOverloads d₁ d₂)
  | _, _ => false

/-- Correspondence as a relation, one constructor per case of
[basic.scope.scope]/4: two functions that declare corresponding
overloads, two function templates that do, and two declarations of one
name that the paragraph's exceptions do not separate. -/
@[specification]
inductive Corresponds : Decl → Decl → Prop where
  /-- Two function declarations with the same name and parameter-type-list. -/
  | overloads (n : String) (ps : List Ty) (s t : Scope) :
      Corresponds (.function n ps s) (.function n ps t)
  /-- Two function template declarations with the same name, equivalent
  template-heads, parameter lists, return types and constraints. -/
  | templateOverloads (f g : FunctionTemplate) (hn : f.name = g.name)
      (hh : headsEquivalent f.head g.head = true) (hp : f.params = g.params) (hr : f.ret = g.ret)
      (hc : f.constraint = g.constraint) : Corresponds (.functionTemplate f) (.functionTemplate g)
  /-- Two declarations of one name, neither a type against a variable or
  function, and not both functions or function templates. -/
  | sameName (d₁ d₂ : Decl) (n : String) (h₁ : d₁.name? = some n) (h₂ : d₂.name? = some n)
      (ht₁ : ¬ (d₁.declaresType = true ∧ d₂.declaresNonType = true))
      (ht₂ : ¬ (d₂.declaresType = true ∧ d₁.declaresNonType = true))
      (hf : ¬ (d₁.declaresFunction = true ∧ d₂.declaresFunction = true)) : Corresponds d₁ d₂

attribute [std rule "basic.scope.scope#4"] Corresponds.overloads
attribute [std rule "basic.scope.scope#4"] Corresponds.templateOverloads
attribute [std rule "basic.scope.scope#4"] Corresponds.sameName

/-- The shapes on which `correspondingOverloads` holds. -/
theorem correspondingOverloads_iff (d₁ d₂ : Decl) :
    correspondingOverloads d₁ d₂ = true ↔
      (∃ n m ps s t, d₁ = .function n ps s ∧ d₂ = .function m ps t) ∨
      (∃ f g, d₁ = .functionTemplate f ∧ d₂ = .functionTemplate g ∧
        headsEquivalent f.head g.head = true ∧ f.params = g.params ∧ f.ret = g.ret ∧
        f.constraint = g.constraint) := by
  cases d₁ <;> cases d₂ <;> simp [correspondingOverloads, and_assoc] <;> exact ⟨Eq.symm, Eq.symm⟩

/-- The function computes the relation. -/
theorem corresponds_iff (d₁ d₂ : Decl) : corresponds d₁ d₂ = true ↔ Corresponds d₁ d₂ := by
  constructor
  · intro h
    unfold corresponds at h
    cases hn₁ : d₁.name? with
    | none => simp [hn₁] at h
    | some n =>
      cases hn₂ : d₂.name? with
      | none => simp [hn₁, hn₂] at h
      | some m =>
        simp only [hn₁, hn₂, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.or_eq_true,
          Bool.and_eq_false_iff] at h
        obtain ⟨⟨⟨rfl, ht₁⟩, ht₂⟩, hf⟩ := h
        rcases hf with hf | hf
        · refine .sameName d₁ d₂ n hn₁ hn₂ ?_ ?_ ?_
          · rintro ⟨a, b⟩; simp_all
          · rintro ⟨a, b⟩; simp_all
          · rintro ⟨a, b⟩; simp_all
        · rcases (correspondingOverloads_iff d₁ d₂).1 hf with ⟨a, b, ps, s, t, rfl, rfl⟩ |
            ⟨f, g, rfl, rfl, hh, hp, hr, hc⟩
          · simp only [Decl.name?, Option.some.injEq] at hn₁ hn₂
            subst hn₁ hn₂
            exact .overloads _ _ _ _
          · simp only [Decl.name?, Option.some.injEq] at hn₁ hn₂
            exact .templateOverloads f g (hn₁.trans hn₂.symm) hh hp hr hc
  · intro h
    cases h with
    | overloads n ps s t => simp [corresponds, Decl.name?, correspondingOverloads, Decl.declaresType,
        Decl.kind?]
    | templateOverloads f g hn hh hp hr hc =>
      simp [corresponds, Decl.name?, correspondingOverloads, Decl.declaresType, Decl.kind?, hn, hh,
        hp, hr, hc]
    | sameName d₁ d₂ n h₁ h₂ ht₁ ht₂ hf =>
      simp only [corresponds, h₁, h₂, beq_self_eq_true, Bool.true_and]
      revert ht₁ ht₂ hf
      cases d₁.declaresType <;> cases d₂.declaresNonType <;> cases d₂.declaresType <;>
        cases d₁.declaresNonType <;> cases d₁.declaresFunction <;> cases d₂.declaresFunction <;>
        simp

/-! ## Conflicts -/

/-- The linkage of a name: external, module, internal or none. -/
inductive Linkage where
  | external
  | module
  | internal
  | none
  deriving Repr, DecidableEq, Inhabited

/-- The linkage of the name a declaration introduces. The fragment has no
`static`, no unnamed namespace, no module and no non-inline `const`
variable, so every name that belongs to a namespace scope has external
linkage, and a member has its class's ([basic.link]/3 to /5). A partial
specialization, a use, a dependent call and a referring declaration
introduce no name. -/
@[std rule "basic.link#4"]
def Decl.linkage : Decl → Linkage
  | .class .. | .classTemplate .. | .function .. | .functionTemplate _ | .object .. | .lookup _
  | .lookupHard _ | .concept .. => .external
  | .instance .. | .use .. | .dependentCall .. | .refersTo _ => .none

/-- Two declarations of one entity declare the same kind of entity: a
variable with a variable, a function with a function, a class template
with a class template, and so on. -/
@[std rule "basic.link#11"]
def sameKind (d₁ d₂ : Decl) : Bool := d₁.kind? == d₂.kind?

/-- Two declarations declare the same entity when they correspond, have
the same target scope, both declare names with external linkage, and
declare the same kind of entity, as two declarations of one entity must.
Module linkage is out of the fragment. Corresponding declarations of
different kinds in one scope are a conflict, not a redeclaration. -/
@[std rule "basic.link#8"]
def sameEntity (d₁ d₂ : Decl) : Bool :=
  corresponds d₁ d₂ && d₁.scope == d₂.scope && d₁.linkage == .external &&
    d₂.linkage == .external && sameKind d₁ d₂

/-- Two declarations potentially conflict: they correspond and cause their
shared name to denote different entities, which within one translation
unit means different kinds of entity. A variable and a function of one
name are the case that matters: an operation object and a free function
named alike cannot share a scope. -/
@[std rule "basic.scope.scope#6.sentence-1"]
def potentiallyConflict (d₁ d₂ : Decl) : Bool := corresponds d₁ d₂ && !sameKind d₁ d₂

/-- The pairs of a program bound in one scope that potentially conflict,
the earlier declaration first. -/
@[std rule "basic.scope.scope#6.sentence-2"]
def Program.conflicts : Program → List (Decl × Decl)
  | [] => []
  | d :: ds =>
    (ds.filter fun e => d.scope == e.scope && potentiallyConflict d e).map (d, ·) ++
      Program.conflicts ds

/-- No name is bound to two declarations that potentially conflict. -/
def Program.scopesWellFormed (p : Program) : Prop := p.conflicts = []

instance (p : Program) : Decidable p.scopesWellFormed :=
  inferInstanceAs (Decidable (_ = _))

/-- Well-formed scopes, as a pairwise condition on the declarations. -/
theorem scopesWellFormed_iff (p : Program) :
    p.scopesWellFormed ↔
      p.Pairwise fun a b => (a.scope == b.scope && potentiallyConflict a b) = false := by
  induction p with
  | nil => simp [Program.scopesWellFormed, Program.conflicts]
  | cons d ds ih =>
    simp only [Program.scopesWellFormed, Program.conflicts, List.append_eq_nil_iff,
      List.map_eq_nil_iff, List.filter_eq_nil_iff, List.pairwise_cons, Bool.not_eq_true]
    rw [← ih]
    rfl

/-! ## The overload set -/

/-- The entities a list of declarations declares, one declaration each:
a declaration of an entity already kept is a redeclaration of it and is
dropped. `acc` holds the entities kept so far. -/
def entities.go (acc : List Decl) : List Decl → List Decl
  | [] => []
  | d :: ds => if acc.any (sameEntity · d) then entities.go acc ds else d :: entities.go (d :: acc) ds

/-- The entities a list of declarations declares, one declaration each,
the first: the declarations found form an overload set, and a later
corresponding declaration is a redeclaration of an entity in it. -/
@[std rule "basic.lookup.general#1.sentence-4"]
def entities (l : List Decl) : List Decl := entities.go [] l

/-- The overload set of a name: the candidates, one per entity. -/
def Program.overloadSet (p : Program) (name : String) : List Decl :=
  entities (p.candidates name)

theorem entities_go_sublist (acc l : List Decl) : (entities.go acc l).Sublist l := by
  induction l generalizing acc with
  | nil => exact .refl _
  | cons d ds ih =>
    simp only [entities.go]
    split
    · exact (ih acc).cons d
    · exact (ih (d :: acc)).cons_cons d

theorem entities_sublist (l : List Decl) : (entities l).Sublist l := entities_go_sublist [] l

/-- Nothing kept corresponds to anything in the accumulator, and no two
kept declarations correspond. -/
theorem entities_go_pairwise (l : List Decl) : ∀ acc,
    (∀ a ∈ acc, ∀ b ∈ entities.go acc l, sameEntity a b = false) ∧
      (entities.go acc l).Pairwise fun a b => sameEntity a b = false := by
  induction l with
  | nil => intro acc; simp [entities.go]
  | cons d ds ih =>
    intro acc
    simp only [entities.go]
    split
    · exact ih acc
    · next hno =>
      obtain ⟨hacc, hpw⟩ := ih (d :: acc)
      refine ⟨fun a ha b hb => ?_, .cons (fun b hb => hacc d (by simp) b hb) hpw⟩
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · simp only [List.any_eq_true] at hno
        exact Bool.eq_false_iff.2 fun h => hno ⟨a, ha, h⟩
      · exact hacc a (by simp [ha]) b hb

/-- No two members of an overload set declare the same entity. -/
theorem entities_pairwise (l : List Decl) :
    (entities l).Pairwise fun a b => sameEntity a b = false :=
  (entities_go_pairwise l []).2

theorem overloadSet_pairwise (p : Program) (name : String) :
    (p.overloadSet name).Pairwise fun a b => sameEntity a b = false :=
  entities_pairwise _

/-- With no two declarations of one entity, the entities are the declarations. -/
theorem entities_go_eq_self (l : List Decl) : ∀ acc,
    (∀ a ∈ acc, ∀ b ∈ l, sameEntity a b = false) →
      l.Pairwise (fun a b => sameEntity a b = false) → entities.go acc l = l := by
  induction l with
  | nil => intros; rfl
  | cons d ds ih =>
    intro acc hacc hpw
    rw [List.pairwise_cons] at hpw
    have hno : acc.any (sameEntity · d) = false := by
      simp only [List.any_eq_false]
      intro a ha
      simp [hacc a ha d (by simp)]
    simp only [entities.go, hno, Bool.false_eq_true, ↓reduceIte, List.cons.injEq, true_and]
    refine ih (d :: acc) (fun a ha b hb => ?_) hpw.2
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact hpw.1 b hb
    · exact hacc a ha b (by simp [hb])

/-- Every program whose functions are declared once keeps its candidate
set. -/
theorem entities_eq_self (l : List Decl) (h : l.Pairwise fun a b => sameEntity a b = false) :
    entities l = l :=
  entities_go_eq_self l [] (by simp) h

theorem overloadSet_eq_candidates (p : Program) (name : String)
    (h : (p.candidates name).Pairwise fun a b => sameEntity a b = false) :
    p.overloadSet name = p.candidates name :=
  entities_eq_self _ h

/-- Inserting a declaration that corresponds to an entity already kept,
in the accumulator or among those of the prefix, changes nothing. -/
theorem entities_go_insert (l₁ : List Decl) (d : Decl) : ∀ acc l₂,
    ((∃ e ∈ acc, sameEntity e d = true) ∨ ∃ e ∈ entities.go acc l₁, sameEntity e d = true) →
      entities.go acc (l₁ ++ d :: l₂) = entities.go acc (l₁ ++ l₂) := by
  induction l₁ with
  | nil =>
    intro acc l₂ h
    simp only [entities.go, List.not_mem_nil, false_and, exists_false, or_false] at h
    have : acc.any (sameEntity · d) = true := by
      simp only [List.any_eq_true]; exact h
    simp [entities.go, this]
  | cons x l₁ ih =>
    intro acc l₂ h
    simp only [List.cons_append, entities.go]
    split
    · next hx =>
      simp only [entities.go, hx, ↓reduceIte] at h
      exact ih acc l₂ h
    · next hx =>
      simp only [entities.go, hx, Bool.false_eq_true, ↓reduceIte, List.mem_cons, exists_eq_or_imp] at h
      rw [ih (x :: acc) l₂]
      rcases h with h | h | h
      · exact .inl (by obtain ⟨e, he, hed⟩ := h; exact ⟨e, by simp [he], hed⟩)
      · exact .inl ⟨x, by simp, h⟩
      · exact .inr h

/-- Inserting a declaration that corresponds to an entity already
declared changes nothing: the entity keeps its first declaration. -/
theorem entities_insert_redecl (l₁ : List Decl) (d : Decl) (l₂ : List Decl)
    (h : ∃ e ∈ entities l₁, sameEntity e d = true) :
    entities (l₁ ++ d :: l₂) = entities (l₁ ++ l₂) :=
  entities_go_insert l₁ d [] l₂ (.inr h)

/-- Redeclaration is inert: declaring a function or function template
of an entity the program already declares, in that entity's scope and
anywhere after its first declaration, leaves the overload set of every
name as it was. -/
theorem redeclaration_inert (p₁ p₂ : Program) (d : Decl) (name : String)
    (hre : ∃ e ∈ p₁.overloadSet name, sameEntity e d = true) :
    (p₁ ++ d :: p₂).overloadSet name = (p₁ ++ p₂).overloadSet name := by
  simp only [Program.overloadSet, Program.candidates, List.filter_append, List.filter_cons] at hre ⊢
  cases d <;> dsimp only at hre ⊢ <;> (try simp only [Bool.false_eq_true, ↓reduceIte]) <;>
    (try split) <;> first | exact entities_insert_redecl _ _ _ hre | rfl

/-- A redeclaration changes no call: resolution over the overload set is
the same, whatever the environment and the ranking. -/
theorem redeclaration_inert_resolve (p₁ p₂ : Program) (d : Decl) (name : String)
    (mode : Mode) (env : Env) (r : Ranking Conv) (args : List CallArg) (explicit : List Ty)
    (hre : ∃ e ∈ p₁.overloadSet name, sameEntity e d = true) :
    resolve mode env r ((p₁ ++ d :: p₂).overloadSet name) args explicit =
      resolve mode env r ((p₁ ++ p₂).overloadSet name) args explicit := by
  rw [redeclaration_inert p₁ p₂ d name hre]

/-- Nor the evaluated call, Mandates included. -/
theorem redeclaration_inert_invoke (p₁ p₂ : Program) (d : Decl) (name : String)
    (mode : Mode) (env : Env) (r : Ranking Conv) (args : List CallArg) (explicit : List Ty)
    (hre : ∃ e ∈ p₁.overloadSet name, sameEntity e d = true) :
    invoke mode env r ((p₁ ++ d :: p₂).overloadSet name) args explicit =
      invoke mode env r ((p₁ ++ p₂).overloadSet name) args explicit := by
  rw [redeclaration_inert p₁ p₂ d name hre]

/-! ## What the candidate list got wrong -/

/-- `void f(int); void f(int); void f(char);` and a call `f(1)`. -/
def redeclaredProgram : Program :=
  [ .function "f" [.named "int"], .function "f" [.named "int"], .function "f" [.named "char"] ]

/-- Over the declarations, the call is ambiguous between the two
declarations of one function. Over the overload set it selects that
function. The second declaration corresponds to the first and is the
same entity, so the first reading was the model's error, now repaired. -/
theorem candidates_redeclaration_ambiguous :
    (resolve .text (Env.ofProgram redeclaredProgram) redeclaredProgram.ranking
        (redeclaredProgram.candidates "f") [{ ty := .named "int" }]).map (·.index) =
      .ambiguous [0, 1] ∧
    (resolve .text (Env.ofProgram redeclaredProgram) redeclaredProgram.ranking
        (redeclaredProgram.overloadSet "f") [{ ty := .named "int" }]).map (·.index) =
      .selected 0 :=
  ⟨rfl, rfl⟩

/-- The example of [basic.scope.scope]/4: `void f(int); // #1`,
`void f(Int) {} // defines #1`, `void f(E) {} // OK, another overload`.
The fragment has no type aliases, so `Int` is `int`; the member function
part of the example, with object parameters, is outside it. -/
@[std example "basic.scope.scope#4"]
theorem scope_scope_4_example :
    corresponds (.function "f" [.named "int"]) (.function "f" [.named "int"]) = true ∧
    corresponds (.function "f" [.named "int"]) (.function "f" [.named "E"]) = false := by
  decide

/-- An operation object and a function of its name in one scope
potentially conflict, so the program is ill-formed. A function and a
function template of one name do not: they overload. -/
theorem object_function_conflict :
    potentiallyConflict (.object "fmap") (.function "fmap" [.named "int"]) = true ∧
    potentiallyConflict (.function "fmap" [.named "int"])
      (.functionTemplate { name := "fmap", head := [{ kind := .type }], params := [.param 0] }) =
      false := by
  decide

end Overload
