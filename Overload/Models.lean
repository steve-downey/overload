-- Overload/Models.lean                                               -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Units
import Overload.Requires

/-!
# What satisfies and what models

A sequence of template arguments models a concept when it satisfies it
and meets every semantic requirement of the concept's specification
([res.on.requirements]/1). Satisfaction the model computes; a semantic
requirement it names and takes as a hypothesis, `Laws`. A program whose
validity depends on modelling, where the arguments satisfy but do not
model, is ill-formed, no diagnostic required (/2), and the semantic
requirements of a declaration's constraints must be modeled at the point
of use (/3): the verdict `satisfiedNotModeled` at a call whose selected
candidate's constraint names a concept the deduced arguments satisfy with
a requirement unclaimed.

The vocabulary the library's requirements are written in,
[concepts.equality], is here as named requirements too: equality
preservation, the domain of an expression, stability, which operands an
expression may modify, and the implicit expression variations.
-/

namespace Overload

/-! ## The vocabulary of [concepts.equality] -/

/-- Given equal inputs, the expression results in equal outputs. -/
@[std rule "concepts.equality#1"]
def equalityPreserving : Semantic :=
  { slug := "equality-preserving"
    statement := "given equal inputs, the expression results in equal outputs; its inputs are its operands and its output is its result and every operand it modifies" }

/-- The requirement is stated on the domain of the expression, the inputs
for which it is required to be well-defined. -/
@[std rule "concepts.equality#2"]
def onDomain : Semantic :=
  { slug := "on-domain"
    statement := "the requirement holds on the domain of the expression, the input values for which it is required to be well-defined; other inputs need not be valid" }

/-- Two evaluations with the same input objects, with no modification
between them, have equal outputs. -/
@[std rule "concepts.equality#3"]
def stable : Semantic :=
  { slug := "stable"
    statement := "two evaluations of the expression with the same input objects, absent any explicit intervening modification of them, have equal outputs" }

/-- A constant operand is not modified; a non-constant one may be. -/
@[std rule "concepts.equality#5"]
def nonModifying : Semantic :=
  { slug := "non-modifying"
    statement := "an operand that is a constant lvalue or rvalue is not modified; one that is a non-constant lvalue or rvalue may be, except where otherwise specified" }

/-- The implicit expression variations meet the declared expression's
semantics. -/
@[std rule "concepts.equality#6"]
def implicitVariations : Semantic :=
  { slug := "implicit-expression-variations"
    statement := "where a requires-expression declares an expression non-modifying for a constant lvalue operand, the variations accepting a non-constant lvalue or an rvalue there are required too and meet the same semantics" }

/-- An expression declared in a library requires-expression is required
to be equality-preserving unless its text says otherwise. -/
@[std rule "concepts.equality#4"]
def libraryExpressionsPreserveEquality : List Semantic := [equalityPreserving, stable, nonModifying]

/-! ## Modelling -/

/-- The oracle for semantic requirements: whether the arguments meet one.
Nothing computes it; a theorem that needs a law states it. -/
abbrev Laws := Semantic → List Ty → Prop

namespace Program

/-- `args` model the concept `c`: they satisfy its normal form, and meet
every semantic requirement modelling it needs. -/
@[std rule "res.on.requirements#1"]
def models (p : Program) (env : Env) (laws : Laws) (c : String) (args : List Ty) : Prop :=
  Constraint.satisfied env.atomic [] (p.normalize (.conceptId c args)) = .ok true ∧
    ∀ law ∈ p.laws c, laws law args

/-- The concept-ids a call's validity depends on: those the selected
candidate's constraint-expression names, with the deduced arguments
substituted. A non-template candidate, or one with no constraint, depends
on none. -/
@[std rule "res.on.requirements#3"]
def conceptUses (decls : List Decl) (c : Candidate) : List (String × List Ty) :=
  match decls[c.index]?, c.specialization with
  | some (.functionTemplate ft), some sp =>
    ((ft.constraint.map Constraint.conceptIds).getD []).map fun (n, as) => (n, as.map (Ty.subst sp.args))
  | _, _ => []

/-- What a case claims about its types: that the arguments meet the
semantic requirement. The analogue of the atomics table, for laws. -/
abbrev Claims := List (Semantic × List Ty)

/-- The verdicts at a call: for each concept the selected candidate's
constraint names at the deduced arguments, if the arguments satisfy it
and a semantic requirement modelling it needs is not claimed for them,
the program is ill-formed, no diagnostic required. -/
@[std rule "res.on.requirements#2" "res.on.requirements#3"]
def modelVerdicts (p : Program) (env : Env) (claims : Claims) (decls : List Decl) (args : List CallArg)
    (explicit : List Ty := []) : List IllFormedNdr :=
  match p.call env decls args explicit with
  | .selected c =>
    (conceptUses decls c).flatMap fun (n, as) =>
      if Constraint.satisfied env.atomic [] (p.normalize (.conceptId n as)) == .ok true then
        (p.laws n).filterMap fun law =>
          if claims.contains (law, as) then none else some (.satisfiedNotModeled n as law)
      else []
  | _ => []

end Program

/-- Modelling implies satisfying: the one direction the text gives. The
converse needs every semantic requirement of the concept's specification,
which nothing in the language decides. -/
@[std theorem "res.on.requirements#1"]
theorem models_satisfies (p : Program) (env : Env) (laws : Laws) (c : String) (args : List Ty)
    (h : p.models env laws c args) :
    Constraint.satisfied env.atomic [] (p.normalize (.conceptId c args)) = .ok true :=
  h.1

/-- Modelling a concept is modelling each concept its body is defined in
terms of, as far as the laws go: a law of the latter is a law of the
former. -/
theorem models_laws_of_body (p : Program) (env : Env) (laws : Laws) (c : String) (args : List Ty)
    (h : p.models env laws c args) (law : Semantic) (hl : law ∈ p.laws c) : laws law args :=
  h.2 law hl

/-! ## The example of [concepts.equality]/8 -/

/-- `template <class T> concept C = requires(T a, T b, const T c, const T d)
{ c == d; a = std::move(b); a = c; };`, and a `T` whose `operator==` takes
`const T&` and deletes the `T&` overload. The fragment has no operators,
so the comparison is a residue atom the case's table holds true; the
concept's specification requires the implicit expression variations. -/
def equalityExample : Program :=
  [ .class "T"
  , .conceptDef "C" 1 (.atomic "comparable_and_assignable" [.param 0])
  , .semantic "C" implicitVariations
  , .functionTemplate { name := "f", head := [{ kind := .type }], params := [.param 0]
                        constraint := some (.conceptId "C" [.param 0]) } ]

/-- The environment in which `T`'s stated expressions are valid. -/
def equalityEnv : Env := Env.full equalityExample [("comparable_and_assignable", [.named "T"], true)]

set_option maxRecDepth 20000 in
/-- `T` satisfies `C`, so `f(t)` selects the template; `T` does not model
`C`, since the deleted `operator==(T&)` fails the implicit variation, and
a program whose validity depends on the modelling is ill-formed, no
diagnostic required. Claimed, the variation gives no verdict. -/
@[std example "concepts.equality#8"]
theorem satisfied_not_modeled_example :
    (equalityExample.call equalityEnv (equalityExample.candidates "f") [{ ty := .named "T" }]).map
        (·.index) = .selected 0 ∧
    equalityExample.modelVerdicts equalityEnv [] (equalityExample.candidates "f") [{ ty := .named "T" }] =
      [.satisfiedNotModeled "C" [.named "T"] implicitVariations] ∧
    equalityExample.modelVerdicts equalityEnv [(implicitVariations, [.named "T"])]
      (equalityExample.candidates "f") [{ ty := .named "T" }] = [] := by
  refine ⟨by decide, by decide, by decide⟩

/-- The verdict in general: at a call that selects a template constrained
by a concept the deduced arguments satisfy, each law of the concept not
claimed for them is a verdict, and a claimed one is none. -/
@[std theorem "res.on.requirements#2"]
theorem satisfied_not_modeled_verdict (p : Program) (env : Env) (claims : Program.Claims)
    (decls : List Decl) (args : List CallArg) (explicit : List Ty) (c : Candidate) (n : String)
    (as : List Ty) (law : Semantic)
    (hsel : p.call env decls args explicit = .selected c)
    (huse : (n, as) ∈ Program.conceptUses decls c)
    (hsat : Constraint.satisfied env.atomic [] (p.normalize (.conceptId n as)) = .ok true)
    (hlaw : law ∈ p.laws n) :
    (IllFormedNdr.satisfiedNotModeled n as law ∈ p.modelVerdicts env claims decls args explicit ↔
      (law, as) ∉ claims) := by
  simp only [Program.modelVerdicts, hsel, List.mem_flatMap]
  constructor
  · rintro ⟨⟨n', as'⟩, _, h⟩
    split at h
    · simp only [List.mem_filterMap] at h
      obtain ⟨law', _, h⟩ := h
      split at h
      · cases h
      · simp only [Option.some.injEq, IllFormedNdr.satisfiedNotModeled.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simpa using ‹¬ claims.contains (law', as') = true›
    · cases h
  · intro hn
    refine ⟨(n, as), huse, ?_⟩
    simp only [hsat, beq_self_eq_true, ↓reduceIte, List.mem_filterMap]
    refine ⟨law, hlaw, ?_⟩
    simp [hn]

end Overload
