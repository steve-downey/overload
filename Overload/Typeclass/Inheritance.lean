-- Overload/Typeclass/Inheritance.lean                                -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Erasure
import Overload.Typeclass.Routes

/-!
# Inheritance between instance types

May instance types for related typeclasses be related by inheritance?
The general answer is `inheritance_erasure`, in `Overload/Erasure.lean`:
inside the exact-type fragment, inheritance between instance types is only
an implementation convenience. This module holds the typeclass side of the
question: the ways erasure changes an outcome outside the fragment, each
with the instance types of the plan's leaks as its program.

* Leak 1, rank beats refinement: a function that names an Applicative
  instance type concretely wins at that type and loses to a generic
  template at a Monad instance type derived from it, because an exact
  match beats a derived-to-base conversion before the non-template
  preference is consulted (`rank_beats_refinement`).
* A function naming a base instance type accepts the derived one, and
  nothing once the derivation is erased (`erasure_needs_exact_type`).
* Leak 2, deduction from a derived class: a parameter of the form
  `derive_functor<I>` deduces `I` from a Monad instance type derived from
  `derive_functor<opt_impl>` ([temp.deduct.call]/4), and does not once the
  derivation is replaced by composition (`derived_class_deduction`).
* Superclass coherence cannot be an identity: a Functor retrieved from a
  stronger instance is a different template argument from the canonical
  Functor instance, so the two can agree only in behaviour
  (`superclass_identity`).

Access to a protected base, which `derive_functor` uses, is in
`Overload/Access.lean`: it turns a selection into an ill-formed call, not
into a candidate that is not viable.
-/

namespace Overload.Typeclass

/-! ## Inheritance leak 1: rank beats the preference for a refinement -/

/-- An Applicative instance type derived from a Functor one, a Monad
instance type derived from that, a generic `use(const T&)` and one that
names the Applicative instance type concretely. -/
def rankLeak : Program :=
  [ .class "functor_i", .class "applicative_i" [.named "functor_i"], .class "monad_i" [.named "applicative_i"]
  , .functionTemplate { name := "use", head := [{ kind := .type }], params := [.lref (.const (.param 0))] }
  , .function "use" [.lref (.const (.named "applicative_i"))] ]

/-- Leak 1 of the plan's instance inheritance: at the Applicative instance
type, the non-template overload naming it wins the tie; at the Monad
instance type derived from it, the generic template wins, because an
exact match beats a derived-to-base conversion before the non-template
preference is consulted. Deriving one instance type from another moves
the call to the less refined overload. -/
theorem rank_beats_refinement :
    (resolve .text (Env.ofProgram rankLeak) rankLeak.ranking (rankLeak.candidates "use")
        [{ ty := .named "applicative_i", lvalue := true }]).map (·.index) = .selected 1 ∧
      (resolve .text (Env.ofProgram rankLeak) rankLeak.ranking (rankLeak.candidates "use")
        [{ ty := .named "monad_i", lvalue := true }]).map (·.index) = .selected 0 := by
  constructor <;> rfl


/-! ## Outside exact-type use, erasure changes the outcome -/

/-- An Applicative instance type derived from a Functor one, and a
function that names the Functor instance type. -/
def namedBase : Program :=
  [ .class "functor_i", .class "applicative_i" [.named "functor_i"]
  , .function "use" [.lref (.const (.named "functor_i"))] ]

/-- Erasure needs exact-type use: a function naming the base instance type
accepts the derived one by a derived-to-base conversion, and after
erasure it accepts nothing. The conversion is not at exact type, so
`inheritance_erasure` does not apply. -/
theorem erasure_needs_exact_type :
    (resolve .text (Env.ofProgram namedBase) namedBase.ranking (namedBase.candidates "use")
        [{ ty := .named "applicative_i", lvalue := true }]).map (·.index) = .selected 0 ∧
      (resolve .text (Env.ofProgram (namedBase.eraseBases ["applicative_i"]))
        (namedBase.eraseBases ["applicative_i"]).ranking
        ((namedBase.eraseBases ["applicative_i"]).candidates "use")
        [{ ty := .named "applicative_i", lvalue := true }]).map (·.index) = .noMatch := by
  constructor <;> rfl

/-! ## Inheritance leak 2: deduction from a derived class -/

/-- A Monad instance type derived from a Functor instance type
`derive_functor<opt_impl>`, and a function of Functor shape. -/
def derivedShape : Program :=
  [ .classTemplate "derive_functor" [{ kind := .type }], .class "opt_impl"
  , .class "opt_monad_map" [.spec' "derive_functor" [.named "opt_impl"]]
  , .functionTemplate
      { name := "use", head := [{ kind := .type }]
        params := [.lref (.const (.spec' "derive_functor" [.param 0]))] } ]

/-- Leak 2 of the plan's instance inheritance: a parameter of the form
`derive_functor<I>` deduces `I` from a class derived from it, so the
Monad instance type silently matches the Functor-shaped signature. With
the derivation replaced by composition it does not match. The deduction
is from a derived class, so `inheritance_erasure` does not apply. -/
theorem derived_class_deduction :
    (resolve .text (Env.ofProgram derivedShape) derivedShape.ranking
        (derivedShape.candidates "use") [{ ty := .named "opt_monad_map", lvalue := true }]).map
        (·.index) = .selected 0 ∧
      (resolve .text (Env.ofProgram (derivedShape.eraseBases ["opt_monad_map"]))
        (derivedShape.eraseBases ["opt_monad_map"]).ranking
        ((derivedShape.eraseBases ["opt_monad_map"]).candidates "use")
        [{ ty := .named "opt_monad_map", lvalue := true }]).map (·.index) = .noMatch := by
  constructor <;> rfl

/-! ## Superclass coherence is a law, not an identity -/

/-- A Functor retrieved from a stronger instance, `derive_functor<M>`, is
a different object from the canonical Functor instance, so pinning one
or the other gives different specializations of the same template. The
two can agree only in behaviour, which the language does not check:
superclass coherence is an obligation on instance authors. -/
theorem superclass_identity (env : Env) (tc name canonical derived : String) (c : Ty)
    (x : CallArg) (hc : c.isType = true) (hcd : c.dependent = false) (hcF : c.formed = true)
    (hcr : c.isRef = false) (hne : canonical ≠ derived) :
    deduceTemplate env (pinTemplate tc name) [c, .ref (.named canonical)] [x] ≠
      deduceTemplate env (pinTemplate tc name) [c, .ref (.named derived)] [x] := by
  rw [pinned_deduce env tc name canonical c x hc hcd hcF hcr,
    pinned_deduce env tc name derived c x hc hcd hcF hcr]
  intro h
  simp [pinSpec] at h
  exact hne h


end Overload.Typeclass
