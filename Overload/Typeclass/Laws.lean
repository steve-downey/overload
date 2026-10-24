-- Overload/Typeclass/Laws.lean                                       -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Typeclass.ValueNature
import Overload.Models

/-!
# The typeclass laws as semantic requirements

The algebraic laws of Functor, Applicative and Monad, and the
superclass-agreement law the plan's inheritance section calls a law on
instance authors, as `Semantic`s attached to the encoding's concepts. The
Standard does not state them, so they carry no citation; their source is
beman.transpose's documentation, named in each statement. Nothing decides
them: an instance that has the shape satisfies the concept, an instance
that keeps the laws models it, and the difference is the verdict of
[res.on.requirements]/2 at any algorithm whose validity depends on the
modelling.

`#owes` on the headline theorems of lookup, `coherence` and `stability`,
lists no law: coherence of the lookup is a fact about declarations, owed
by no one. The superclass-coherence obligation is the opposite: a theorem
with its law as hypothesis, and a verdict without it.
-/

namespace Overload.Typeclass

/-! ## The laws -/

/-- `fmap(identity, x)` is `x`. -/
def functorIdentity : Semantic :=
  { slug := "functor-identity"
    statement := "fmap(std::identity{}, x) is equal to x (beman.transpose, Functor laws)" }

/-- `fmap(f, fmap(g, x))` is `fmap(f ∘ g, x)`. -/
def functorComposition : Semantic :=
  { slug := "functor-composition"
    statement := "fmap(f, fmap(g, x)) is equal to fmap(compose(f, g), x) (beman.transpose, Functor laws)" }

/-- `pure` is a unit for `ap`, and `ap` composes. -/
def applicativeIdentity : Semantic :=
  { slug := "applicative-identity"
    statement := "ap(pure(std::identity{}), v) is equal to v (beman.transpose, Applicative laws)" }

def applicativeHomomorphism : Semantic :=
  { slug := "applicative-homomorphism"
    statement := "ap(pure(f), pure(x)) is equal to pure(f(x)) (beman.transpose, Applicative laws)" }

/-- `pure` is a left and right unit for `bind`, and `bind` associates. -/
def monadLeftIdentity : Semantic :=
  { slug := "monad-left-identity"
    statement := "bind(pure(a), f) is equal to f(a) (beman.transpose, Monad laws)" }

def monadRightIdentity : Semantic :=
  { slug := "monad-right-identity"
    statement := "bind(m, pure) is equal to m (beman.transpose, Monad laws)" }

def monadAssociativity : Semantic :=
  { slug := "monad-associativity"
    statement := "bind(bind(m, f), g) is equal to bind(m, [&](auto x) { return bind(f(x), g); }) (beman.transpose, Monad laws)" }

/-- The Functor an instance derives for its superclass behaves as the
canonical Functor instance where one exists: the two are different
template arguments, so they can agree only in behaviour
(`superclass_identity`). -/
def superclassAgreement : Semantic :=
  { slug := "superclass-agreement"
    statement := "the Functor operations of derive_functor<M> agree in behaviour with those of the canonical Functor instance for M's container, where one exists (docs/plan.md, instance inheritance, leak 3)" }

/-! ## The concepts with their laws -/

/-- Functor, Applicative and Monad as concepts on an instance's shape,
each with its laws, and the superclass agreement on Monad, whose
`as_functor` derives the Functor. -/
def lawfulConcepts : Program :=
  refinementConcepts ++
  [ .semantic "Functor" functorIdentity, .semantic "Functor" functorComposition
  , .semantic "Applicative" applicativeIdentity, .semantic "Applicative" applicativeHomomorphism
  , .semantic "Monad" monadLeftIdentity, .semantic "Monad" monadRightIdentity
  , .semantic "Monad" monadAssociativity, .semantic "Monad" superclassAgreement ]

/-- Modelling Monad is keeping every law down to Functor's: eight in all. -/
theorem monad_laws :
    lawfulConcepts.laws "Monad" =
      [ monadLeftIdentity, monadRightIdentity, monadAssociativity, superclassAgreement
      , applicativeIdentity, applicativeHomomorphism, functorIdentity, functorComposition ] := by
  decide +kernel

/-! ## The superclass-coherence obligation as a theorem -/

/-- An algorithm over a Monad instance, `template <Monad M> void run(const M&)`,
which derives the instance's Functor, and a Monad instance type whose
shape satisfies all three concepts. -/
def monadAlgorithm : Program :=
  lawfulConcepts ++
  [ .class "monad_i"
  , .functionTemplate { name := "run", head := [{ kind := .type }], params := [.lref (.const (.param 0))]
                        constraint := some (.conceptId "Monad" [.param 0]) } ]

/-- The environment: the instance has the shapes. -/
def monadEnv : Env := Env.full monadAlgorithm monadShapes

/-- Every law except superclass agreement, claimed for the instance. -/
def lawsButAgreement : Program.Claims :=
  [ monadLeftIdentity, monadRightIdentity, monadAssociativity, applicativeIdentity
  , applicativeHomomorphism, functorIdentity, functorComposition ].map (·, [.named "monad_i"])

/-- The instance satisfies Monad, so `run(m)` selects the algorithm. With
every law but superclass agreement claimed, the call's validity depends on
a modelling the instance lacks, and the verdict names the law. With the
agreement claimed too, there is no verdict: the obligations table's
undiagnosable row, as a theorem. -/
theorem superclass_coherence_owed :
    (monadAlgorithm.call monadEnv (monadAlgorithm.candidates "run")
        [{ ty := .named "monad_i", lvalue := true }]).map (·.index) = .selected 0 ∧
    monadAlgorithm.modelVerdicts monadEnv lawsButAgreement (monadAlgorithm.candidates "run")
        [{ ty := .named "monad_i", lvalue := true }] =
      [.satisfiedNotModeled "Monad" [.named "monad_i"] superclassAgreement] ∧
    monadAlgorithm.modelVerdicts monadEnv ((superclassAgreement, [.named "monad_i"]) :: lawsButAgreement)
        (monadAlgorithm.candidates "run") [{ ty := .named "monad_i", lvalue := true }] = [] := by
  refine ⟨by decide, by decide +kernel, by decide +kernel⟩

/-- An instance with the shape and no law claimed gets every law as a
verdict: satisfying is not modelling. -/
theorem shape_without_laws :
    (monadAlgorithm.modelVerdicts monadEnv [] (monadAlgorithm.candidates "run")
        [{ ty := .named "monad_i", lvalue := true }]).length = 8 := by
  decide +kernel

end Overload.Typeclass
