-- Overload/Typeclass/ValueNature.lean                                -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Typeclass.Encoding
import Overload.Identity
import Overload.Requires

/-!
# The value nature of an instance type, and what a constraint owes

Phase 12 on the encoding. An instance type of beman.transpose is a class
with no data members, whose operations are static members: every special
member of it is implicitly declared, not deleted and trivial, so it is
trivially copyable, empty and standard-layout, and the value route's
copy of it costs nothing (`instance_shape_regular`). An instance type
that holds a reference, a stateful instance capturing by reference, is
structural for the value route and still not assignable: the two
notions do not coincide (`reference_member_instance`).

The `callable-copying` obligation says an instance that copies its
callable says so in its constraint. With `is_copy_constructible` a
judgement, the rule is a theorem: the trait as a constraint makes the
call not viable at a callable whose copy constructor is deleted, where
the same trait as a Mandate, the body's copy, makes the call ill-formed
(`copy_constraint_shields`).

Refinement in the encoding is a concept on the instance's shape. With
concept-ids normalized, the Monad concept's normal form contains the
Functor concept's atoms, so Monad subsumes Functor without any identity
between names (`refinement_normalizes`), and a call constrained by
Functor and one by Monad select the Monad overload at a Monad instance
(`refinement_selects`). A requires-expression probing a member says what
the member call says (`member_probe_accurate`), which is the
accurate-members obligation stated as the Standard states it.
-/

namespace Overload.Typeclass

/-! ## The shape of an instance type -/

/-- Three instance types with no data members: a Functor instance, an
Applicative instance derived from it, a Monad instance derived from that. -/
def instanceShapes : Program :=
  [ .class "functor_i", .class "applicative_i" [.named "functor_i"]
  , .class "monad_i" [.named "applicative_i"] ]

/-- An instance type with no data members and no declared special member
has every special member defaulted, not deleted and trivial: it is
trivially copyable, empty, standard-layout, and default, copy and move
constructible, through a base as well as flat. -/
theorem instance_shape_regular :
    [Ty.named "functor_i", .named "applicative_i", .named "monad_i"].all (fun t =>
      instanceShapes.valueNature t &&
      instanceShapes.trait .isTriviallyCopyable [t] == .ok true &&
      instanceShapes.trait .isEmpty [t] == .ok true &&
      instanceShapes.trait .isStandardLayout [t] == .ok true &&
      instanceShapes.trait .isDefaultConstructible [t] == .ok true &&
      instanceShapes.trait .isCopyConstructible [t] == .ok true &&
      instanceShapes.trait .isTriviallyMoveConstructible [t] == .ok true) = true := by
  decide

/-- An instance type holding a reference: `struct ref_i { int& r; };`. -/
def referenceInstance : Program :=
  [.class "ref_i", .member (.named "ref_i") { name := "r", ty := .lref (.named "int") }]

/-- Such an instance type is structural, so the value route admits it as a
constant template argument, and it is still neither default
constructible nor assignable: structural and value nature are different
properties. -/
theorem reference_member_instance :
    referenceInstance.structural (.named "ref_i") = true ∧
    referenceInstance.trait .isCopyConstructible [.named "ref_i"] = .ok true ∧
    referenceInstance.trait .isDefaultConstructible [.named "ref_i"] = .ok false ∧
    referenceInstance.trait .isCopyAssignable [.named "ref_i"] = .ok false ∧
    referenceInstance.valueNature (.named "ref_i") = false := by
  decide

/-! ## A polymorphic or abstract instance type -/

/-- An instance type with a virtual operation, an abstract one, a
concrete instance derived from it, and an algorithm taking the abstract
instance by value and one taking it by reference to `const`. -/
def polymorphicInstances : Program :=
  [ .class "virtual_i", .function "fmap" [] [.class "virtual_i"] .virtual
  , .class "abstract_i", .function "fmap" [] [.class "abstract_i"] .pure
  , .class "concrete_i" [.named "abstract_i"], .function "fmap" [] [.class "concrete_i"] .override
  , .function "by_value" [.named "abstract_i"]
  , .function "by_reference" [.lref (.const (.named "abstract_i"))] ]

/-- A polymorphic instance type keeps value nature, every special member
defaulted and not deleted, and stays structural, so the value route
admits it as a constant template argument; but none of its special
members is trivial, so it is neither trivially copyable nor
standard-layout nor empty: the route's copy of it is a real copy. -/
theorem virtual_instance_costs :
    polymorphicInstances.valueNature (.named "virtual_i") = true ∧
    polymorphicInstances.structural (.named "virtual_i") = true ∧
    polymorphicInstances.trait .isTriviallyCopyable [.named "virtual_i"] = .ok false ∧
    polymorphicInstances.trait .isStandardLayout [.named "virtual_i"] = .ok false ∧
    polymorphicInstances.trait .isEmpty [.named "virtual_i"] = .ok false := by
  decide

/-- An abstract instance type cannot take the value route at all: it is
not constructible, and an algorithm that takes it by value is ill-formed
to call even with a concrete derived instance. Only a reference reaches
the algorithm. -/
theorem abstract_instance_by_reference :
    polymorphicInstances.trait .isConstructible [.named "abstract_i"] = .ok false ∧
    polymorphicInstances.call (Env.ofProgram polymorphicInstances)
        (polymorphicInstances.candidates "by_value") [{ ty := .named "concrete_i", lvalue := true }] =
      .illFormed "a parameter is of abstract class type" ∧
    (polymorphicInstances.call (Env.ofProgram polymorphicInstances)
        (polymorphicInstances.candidates "by_reference") [{ ty := .named "concrete_i", lvalue := true }]).map
        (·.index) = .selected 0 := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## The callable-copying rule -/

/-- A callable whose copy constructor is deleted, and the two ways an
algorithm that copies its callable can say so: a constraint,
`requires std::is_copy_constructible_v<F>`, or the copy in its body, a
Mandate. -/
def copyingAlgorithm (constrained : Bool) : Program :=
  let cond : Constraint := .trait .isCopyConstructible [.param 0]
  [ .class "fn", .special (.named "fn") { kind := .copyCtor, body := .deleted }
  , .functionTemplate { name := "run", head := [{ kind := .type }], params := [.lref (.const (.param 0))]
                        constraint := if constrained then some cond else none
                        mandate := if constrained then none else some cond } ]

/-- The callable, an lvalue. -/
def callable : CallArg := { ty := .named "fn", lvalue := true }

/-- With the trait in its constraint, the algorithm is not viable at the
callable: a clean no. With the trait as a Mandate, the body's copy, the
call is ill-formed: yes, then fails. -/
theorem copy_constraint_shields :
    (copyingAlgorithm true).call (Env.full (copyingAlgorithm true))
        ((copyingAlgorithm true).candidates "run") [callable] = .noMatch ∧
    ∃ e, (copyingAlgorithm false).call (Env.full (copyingAlgorithm false))
        ((copyingAlgorithm false).candidates "run") [callable] = .illFormed e := by
  refine ⟨by decide, ⟨_, rfl⟩⟩

/-! ## Refinement by normalization -/

/-- Functor, Applicative and Monad as concepts on an instance's shape,
each refining the last by conjunction with its own shape constraint. -/
def refinementConcepts : Program :=
  [ .conceptDef "Functor" 1 (.atomic "functor_shape" [.param 0])
  , .conceptDef "Applicative" 1 (.conj (.conceptId "Functor" [.param 0]) (.atomic "applicative_shape" [.param 0]))
  , .conceptDef "Monad" 1 (.conj (.conceptId "Applicative" [.param 0]) (.atomic "monad_shape" [.param 0])) ]

/-- The Monad concept's normal form subsumes the Functor concept's, and
not the other way round; compared as concept-ids by name, neither
subsumes the other. -/
@[std theorem "temp.constr.normal#1"]
theorem refinement_normalizes :
    Constraint.subsumes (refinementConcepts.normalize (.conceptId "Monad" [.param 0]))
        (refinementConcepts.normalize (.conceptId "Functor" [.param 0])) = true ∧
    Constraint.subsumes (refinementConcepts.normalize (.conceptId "Functor" [.param 0]))
        (refinementConcepts.normalize (.conceptId "Monad" [.param 0])) = false ∧
    Constraint.subsumes (.conceptId "Monad" [.param 0]) (.conceptId "Functor" [.param 0]) = false := by
  decide

/-- `template <Functor T> void use(const T&); template <Monad T> void use(const T&);`
over a Monad instance type whose shape satisfies all three concepts. -/
def refinementOverloads : Program :=
  refinementConcepts ++
  [ .class "monad_i"
  , .functionTemplate { name := "use", head := [{ kind := .type }], params := [.lref (.const (.param 0))]
                        constraint := some (.conceptId "Functor" [.param 0]) }
  , .functionTemplate { name := "use", head := [{ kind := .type }], params := [.lref (.const (.param 0))]
                        constraint := some (.conceptId "Monad" [.param 0]) } ]

/-- The shapes a Monad instance has. -/
def monadShapes : List (String × List Ty × Bool) :=
  [ ("functor_shape", [.named "monad_i"], true), ("applicative_shape", [.named "monad_i"], true)
  , ("monad_shape", [.named "monad_i"], true) ]

/-- At a Monad instance both overloads are viable and the Monad one is
more constrained, so it is selected: refinement works through
normalization alone. -/
theorem refinement_selects :
    (refinementOverloads.call (Env.full refinementOverloads monadShapes)
        (refinementOverloads.candidates "use") [{ ty := .named "monad_i", lvalue := true }]).map (·.index) =
      .selected 1 := by
  decide

/-! ## The member probe -/

/-- A Functor instance type with a static `fmap` taking a callable and a
value of `int`, and a callable type. -/
def probedInstance : Program :=
  [ .class "fn", .class "box_i"
  , .function "fmap" [.lref (.const (.named "fn")), .named "int"] [.class "box_i"] ]

/-- A requires-expression probing `fmap` holds at the arguments the
member accepts and fails at the ones it does not, as the member call
does. -/
theorem member_probe_accurate :
    probedInstance.requirementHolds (Env.ofProgram probedInstance)
        (.memberCall (.named "box_i") "fmap" [.named "fn", .named "int"]) = .ok true ∧
    probedInstance.requirementHolds (Env.ofProgram probedInstance)
        (.memberCall (.named "box_i") "fmap" [.named "fn", .named "box_i"]) = .ok false ∧
    probedInstance.requirementHolds (Env.ofProgram probedInstance)
        (.memberCall (.named "fn") "fmap" [.named "fn", .named "int"]) = .ok false := by
  decide

end Overload.Typeclass
