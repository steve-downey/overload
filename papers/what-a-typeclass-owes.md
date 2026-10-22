---
title: "What a Typeclass Owes: Obligations of a Library Typeclass Encoding, from a Formal Model of Overload Resolution"
document: DXXXXR0
date: 2026-10-22
audience: LEWG, EWG
author:
  - name: Steve Downey
    email: <sdowney@gmail.com>
toc: true
toc-depth: 2
references:
  - id: BEMAN-TRANSPOSE
    citation-label: beman.transpose
    title: "beman.transpose: typeclasses for C++ as a library"
    URL: https://github.com/bemanproject/typeclass
---

```{=latex}
% Latin Modern Mono has no U+2227; typeset it from math, keeping the
% monospace font for the rest of each code span.
\catcode`\∧=\active
\protected\def∧{\ensuremath{\wedge}}
```

# Abstract

Typeclasses can be written in C++ as a library. An instance is a partial
specialization of a variable template whose primary is `std::false_type`,
and a user calls the instance's members. Each operation is also an object
whose call operator finds the instance through a defaulted constant
template parameter. beman.transpose
[@BEMAN-TRANSPOSE] is built this way. This paper reports what a formal model of the Standard's
selection rules says about that encoding: what it guarantees by
construction, what it leaves as an obligation on the typeclass author, the
instance author, the user and the author of an algorithm written against a
typeclass, and which of those obligations no compiler can check.

The model is written in Lean 4. It transcribes name lookup in namespace
and class scopes, argument-dependent lookup, template argument
conversion, template argument deduction, substitution failure,
constraints and subsumption, Mandates, partial ordering, partial
specialization matching and overload resolution, each rule cited by
stable name and paragraph against the working draft [@N5054]. Its
predictions were checked against GCC 13 to 16 and Clang 17 to 24 on 125
generated programs.

The short form of the result is that the design is sound because it puts
a variable everywhere C++ would otherwise build an overload set, and its
hazards appear exactly where an overload set comes back.

# Introduction

A typeclass names a set of operations and the laws they obey, and lets
each type supply them separately from the type's definition. Haskell
selects the implementation by type; C++ has no such mechanism in the
language, but it has three that can be combined to the same effect:
partial specialization matching to pick an instance for a type, default
template arguments to look it up at a call, and constraints to make a
call with no instance not viable.

The questions this paper answers are the ones a designer has to answer
before recommending the technique:

- Is instance selection coherent: does a type get at most one instance,
  and never a silent choice between two?
- Is it stable: does adding an instance somewhere change only the calls
  it should change?
- What must each party do so that these hold, and which of those duties
  does a compiler check?

The answers come from proofs about a model of the rules, not from
experiments with one compiler. Where a compiler disagrees with the text,
the disagreement is reported against the cited sentence.

# The encoding

A typeclass has two layers.

The instance is the bundle of operations, and it is the interface a user
calls. A lookup variable template names it, with `std::false_type` as the
instance for types that have none:

```cpp
template <class T>
inline constexpr auto functor = std::false_type{};

template <class V>
inline constexpr auto functor<std::optional<V>> = OptionalFunctorMap<V>{};
```

The instance's operations are its members. A user names the instance of
record and calls them:

```cpp
const auto &app = applicative<std::optional<int>>;
auto sum = app.invoke(sum3, std::optional{1}, std::optional{2},
                      std::optional{3});
```

An instance is usually built from an implementation that supplies a
minimal basis, through a derivation base that supplies the rest. The
derivation base takes the implementation as a protected base, and the
instance re-exposes the basis with using-declarations:

```cpp
template <class V>
struct optional_applicative_map
    : derive_applicative<optional_applicative_impl<V>> {
    using optional_applicative_impl<V>::invoke;
    using optional_applicative_impl<V>::pure;
};
```

Each named operation is also an operation object of its own, a second
interface over the first, with one call operator. The call operator finds the instance through a trailing
constant template parameter, a reference defaulted to the lookup, and is
constrained on the call through it:

```cpp
struct fmap_fn {
    template <class F, class T,
              const auto &TC = functor<std::remove_cvref_t<T>>>
        requires requires { TC.fmap(std::declval<F>(), std::declval<T>()); }
    constexpr auto operator()(F &&f, T &&t) const {
        return TC.fmap(std::forward<F>(f), std::forward<T>(t));
    }
};
inline constexpr fmap_fn fmap{};
```

The operation object is shaped like a customization point object, but it
does not dispatch through argument-dependent lookup or `tag_invoke`. It
dispatches through the lookup variable.

Two other ways to supply an instance exist beside the canonical lookup.
A caller can name an instance object and call its member, `tc.fmap(f, v)`.
And an operation can take the instance as a trailing by-value argument
whose type defaults to the type of the looked-up instance, as
`traverse` does with its policy.

# The model

The model gives each mechanism twice: as an inductive relation whose
constructors transcribe the Standard's sentences, each cited, and as an
executable function, with a proof that the two agree. Every headline
theorem is checked to rest on no unproven assumption.

Where the Standard needs the meaning of an expression the model does not
model, such as whether a concept is satisfied, an oracle answers, and the
oracle says whether a failure is in the immediate context. Programs are
lists of declarations, so "declared before use" is a property the model
can state.

The executable model emits each test case as a C++ translation unit whose
`static_assert`s encode the model's expectation, and the case is compiled
with each compiler. The expectation is always what the text says. A
compiler that disagrees is reported, never outvoted.

# Why the design works: a variable cannot be overloaded

The encoding puts a variable at each point where C++ would otherwise
build an overload set, and most of its good behaviour follows.

**The operation object.** `fmap` is a variable. Name lookup for
`fmap(f, x)` finds one entity, so the call has one candidate, the
object's call operator. Argument-dependent lookup does not run when
ordinary lookup finds an object ([basic.lookup.argdep]/1), and the
candidates of a call on an object are its class's call operators and
nothing else ([over.call.object]/1), so nobody can add an overload that
competes with it. The model proves this from the lookup rules, and
proves the contrast: written as a function template, `fmap` admits a
user's `fmap` declared beside the user's class, found through the
argument's namespace, and the user's wins.

**The instance.** `functor<T>` is a variable template. Choosing an
instance is partial specialization matching, not overload resolution, so
conversion ranking, argument-dependent lookup and the preference for
non-templates never touch it. The model proves:

- *Coherence.* For a type, lookup selects the most specialized matching
  instance, or reports ambiguity, or finds none and yields the primary. It
  never chooses silently between unordered instances.
- *Stability.* Declaring an instance moves lookup only at types the new
  instance matches, and there only to the new instance or to ambiguity.
  Lookups of other typeclasses do not move.
- *Separability.* For any two conversion rankings, if both select a
  candidate at a position, it is the same candidate with the same template
  arguments. The ranking decides which candidate wins; it cannot change
  the instance a candidate carries.

**The call.** At the call surface the same results hold for the operation
object. Deducing it follows lookup at the argument's type with cv and
reference qualifiers removed. It succeeds when an instance is selected,
fails softly, making the call not viable, when none is, and fails hard only
when lookup is ambiguous. Declaring an instance leaves a call unchanged
unless the instance matches the call's key. When it does, the call becomes
viable through it, or is ill-formed by ambiguity.

**The members.** With an instance in hand, `app.invoke(...)` or
`TC.fmap(...)` is member lookup in one class, which nothing at namespace
scope can join. Argument-dependent lookup applies only to an unqualified
name ([basic.lookup.argdep]/1), and member lookup stops at the first class
whose scope declares the name ([class.member.lookup]/3), whatever the
signatures and constraints of what the bases declare. The instance's
using-declaration of its implementation's `invoke` therefore hides the
derivation base's, and the call has one template. The model proves the
hiding, and it is a two-edged rule: the same lookup hides
`derive_functor`'s constrained `fmap` behind an unconstrained one that
an instance re-exposes. The member call at the operation object's
constraint the model takes as given, and proves that the object passes
it on unchanged: viable where the member call is valid, not viable where
it is invalid, and ill-formed where checking it is a hard error. The
operation object can add no accuracy the member lacks. That is the one
place where the design relies on its authors more than on its shape, and
the first obligation below on the typeclass author is what makes it
hold.

Every hazard the model found is a place where an overload set comes back.

# Obligations

Each obligation below is a hypothesis some theorem needs that the language
does not guarantee. Each is classed by how it is discharged: by
construction, compiler-checked, library-checkable, or undiagnosable.

## For the typeclass author

- **The members are accurate.** Each member an instance exposes must be
  constrained so that a probe of it fails softly where the call is not
  viable, and succeeds only where it is. The operation object's
  constraint is the member call, so it can be no more accurate than the
  member. A derived member with no constraint and a deduced return type
  fails this: a probe instantiates its body to deduce the type, and an
  error there is not in the immediate context
  ([dcl.spec.auto.general]/15). So does a constraint with an alternative
  weaker than the body it selects. A probe of every typeclass in
  beman.transpose found members of each kind in every derivation base,
  and two members that are wrong about the call, not only about the
  probe. `any_of` with a predicate that cannot be called reports the
  call as valid, and the call fails. The optional Monad's `bind` accepts
  a function that does not return an optional, and returns a plain value.
  Where an implementation supplies only `ap`, the derived `invoke`
  curries the function. It accepts a function that cannot take the
  arguments and returns an unsaturated partial application in the
  context. Three more causes appear when the callable varies. A member
  may copy the callable it is given, as the Standard's algorithms may
  ([algorithms.requirements]/9), but then its constraint has to say the
  copy can be made: `zip_list`'s `invoke` is a hard error for a move-only
  lvalue, and the sender's reports the call valid and then fails. A
  member whose context cannot hold the result has to check for it:
  `invoke` with a function returning `void` names `std::optional<void>`.
  And an operation an instance refuses has to be refused as a
  constraint. The accumulating Applicative for `std::expected` refuses
  `bind` with a `static_assert` in a deduced body, so asking whether that
  object is a Monad is a hard error. beman.transpose has since
  constrained each of these members, and at its current head every
  probe but one answers as required; the one left is a Kleisli
  composition whose constraint ends `|| true`. *Not by construction.*
- **Instances of std types live with the typeclass.** An instance must be
  visible wherever its lookup is used on its type. For a library type the
  type's own header is enough, since every use has to include it. For a
  std type the only header every use is guaranteed to include is the
  typeclass's. An instance in a header of its own, as beman.transpose
  declares the instances for `std::array`, `std::expected`,
  `std::simd::basic_vec` and, for folding and traversal, `std::vector`,
  makes a program that includes it late, or in some translation units
  and not others, ill-formed with no diagnostic required. GCC diagnoses
  the late case. Clang keeps the first answer, and the instance stays
  invisible after its header is included. This is Haskell's orphan rule
  with a well-formedness consequence. beman.transpose's answer is to
  declare the instance for a standard type with the type, in a header
  that stands in for the standard one as `tuple_size` comes with
  `<array>`, and to make including that header the program's
  obligation; its umbrella header includes them all. The hazard is
  documented rather than designed away. *Undiagnosable.*
- **The primary is soft.** The lookup's primary must be a value such as
  `std::false_type`, not a `static_assert`. A default template argument is
  substituted before constraints are checked, so a requires-clause on the
  same template cannot guard it. A hard primary makes every call ill-formed
  whose deduction reaches the lookup, including calls that would have
  chosen another overload. *By construction in beman.transpose.*
- **The default is shapeless.** A missing instance makes the call not
  viable only because `std::false_type` has no `fmap`. *Library-checkable:
  one `static_assert` per typeclass that the primary fails the shape.*
- **The lookup key is normalized.** The lookup is at
  `std::remove_cvref_t<T>`, so every spelling of a type reaches one
  instance. *By construction.*
- **No other candidate reaches the lookup.** Stability at the call surface
  needs the call's other candidates not to look the instance up. An
  operation object with one call operator meets this by theorem: lookup
  binds the name to the object, argument-dependent lookup does not apply,
  and the class's call operators are the whole candidate set. One with
  several, as beman.transpose's `fold_map` and `combine_all` have, meets
  it when they differ by arity and each puts the lookup default after a
  parameter a shorter call cannot deduce: that overload fails before it
  reaches the lookup. With the default first, it reaches the lookup in a
  call meant for another overload, and an ambiguous lookup makes that
  call ill-formed. If a named operation were a function template or an
  overload set, anyone could add an overload, and each added overload
  would have to stay away from the lookup and be visible to every
  dependent call that could find it; see [Across translation units].
- **Refinement is visible.** Write a refinement between conditions as
  constraints, so subsumption can see it. An `enable_if` encoding of the
  same condition has the same viable set, and loses every ordering a
  requires-clause would win, without a diagnostic. *Convention.*

## For the instance author

- **Canonicity.** No two instances may match a type with neither more
  specialized. *Compiler-checked under the text*, at the lookup and at
  every call that substitutes it. At the call surface the compilers do not
  check it; see [Implementations].
- **Expose the accurate member.** A using-declaration of an
  implementation's member hides the derivation base's member of that
  name, by rule and whatever the two members' constraints
  ([class.member.lookup]/3). That is right when the implementation's
  member is the accurate one, as for every Applicative `invoke` in
  beman.transpose, and wrong when it is not: the optional and vector
  Functor implementations' `fmap` is unconstrained, and re-exposing it
  hides `derive_functor`'s constrained `fmap`. A call with a function
  that cannot take the element is then a hard error, through the member
  call and through the operation object. *Convention.*
- **Visibility.** Every instance must be declared before any use of its
  lookup, the same in every translation unit. *Undiagnosable*; see
  [Across translation units].
- **Distinct instance types.** The by-value route identifies an instance by
  its type alone, so two instances of one typeclass must be objects of
  different types. *Convention.*
- **Superclass coherence.** A Functor derived from a stronger instance, as
  a Monad's `as_functor` returns, should behave as the canonical Functor
  where one exists. The two are different template arguments, so they can
  agree only in behaviour. *A law; undiagnosable, and the program is
  well-formed either way.*

## For users and the authors of functions on instances

- **Exact-type use.** A signature should take an instance at its deduced
  type and never name an instance type, not even as a base such as
  `derive_functor<I>`, nor an implementation an instance inherits through
  a protected base. See [Inheritance between instance types].
  *Undiagnosable: the program is well-formed and calls what the author did
  not mean.*
- **Soft failure for pinning functions.** A function that takes an instance
  explicitly and has no constraint is viable for a type with no instance,
  and fails in its body. Whoever writes such a function owes the
  constraint.

## For the author of an algorithm

An algorithm written against a typeclass, one that takes an Applicative
or a Monoid and calls its members, is one more operation object over an
instance. It owes what the operation objects owe, and three things more,
from sitting between a caller and an instance it did not choose. The
weighing is for accident: the question for each gap is what an ordinary
mistake does, and what closing it would forbid.

- **State the member calls.** An algorithm that others will constrain
  on should state, as its constraint, the member calls its body makes.
  With that constraint it answers exactly as its members do, call by
  call in the order written, and it is accurate when they are. The order
  is part of the answer: conjunction checks its right operand only when
  the left is satisfied ([temp.constr.op]/2), so a guard written after
  the call it protects protects nothing. beman.transpose's folds test
  for a registered `Monoid` before they name one. An algorithm nobody
  checks owes nothing here: a weaker constraint is a hard error at its
  call, never a program that compiles and should not. *Convention.*
- **Use the instance given.** Every operation on a context comes from
  the object the algorithm was handed. A context can have two
  instances: `std::expected` has a short-circuit Applicative, which the
  lookup finds, and an accumulating one, which a caller passes by name.
  Under the accumulating one, a single call of the `invoke` operation
  object, or of `bind`, in place of the object's member keeps the first
  error and drops the rest, and compiles. The cost stays bounded because
  of a rule on the typeclass author: an alternative instance that
  changes values gets its own carrier, as the zip Applicative has
  `zip_list`, and only one that changes evidence shares a carrier.
  *Undiagnosable.*
- **Use the object passed.** An algorithm that constructs a fresh
  instance from its type assumes the instance has no state. All of
  beman.transpose's typeclass objects are empty, but a caller's may
  carry an allocator, a scheduler or a log. `lifted_monoid` and
  `kleisli_monoid` constructed their own, and a stateful object passed
  by type was never consulted; they now hold the object. Hold the
  object, which costs nothing for an empty one, or require
  `std::is_empty_v`. *Library-checkable.*
- **Pass `std::ref` for identity.** An instance may run a copy of a
  callable, so an algorithm that needs the caller's own object, to count
  or accumulate in it, passes a reference wrapper, as for the Standard's
  algorithms. *Convention.*

# Inheritance between instance types

beman.transpose relates no two instance types by public inheritance, but
inheritance is a choice an implementer can make, and the paper treats it as
allowed. Forbidding it would need a means of enforcement that does not
exist. The question is what it costs.

Within one discipline it costs nothing. Replacing derivation between
instance types by composition changes no call that uses every affected
class at its exact type and never deduces through it as a base. The model
proves this for its fragment. Outside that discipline there are five
hazards. The first, second and fifth are confirmed on every compiler
tested; the third and fourth are theorems about identity, and the fourth
follows C++26, where Clang and GCC currently differ.

**Ranking beats refinement.** A derived-to-base conversion has Conversion
rank, and conversions are compared before the preference for
non-templates or partial ordering.

```cpp
struct functor_i {};
struct applicative_i : functor_i {};
struct monad_i : applicative_i {};

template <class T> void use(const T&);   // #1
void use(const applicative_i&);          // #2

use(applicative_i{});  // #2: conversions tie, the non-template is preferred
use(monad_i{});        // #1: an exact match beats derived-to-base
```

Deriving one instance type from another moved the call to the less
refined overload.

**Deduction from a derived class.** A parameter of class template form
deduces from a class derived from it ([temp.deduct.call]/4).

```cpp
template <class I> struct derive_functor {};
struct opt_impl {};
struct opt_monad_map : derive_functor<opt_impl> {};

template <class I> void use(const derive_functor<I>&);
use(opt_monad_map{});   // deduces I = opt_impl
```

A Monad instance silently matches a Functor-shaped signature.

**Two paths to the superclass.** Slicing an instance to its base gives one
Functor and lookup gives another, and they are different template
arguments.

**Constant-parameter slicing.** A constant template argument is
converted to its parameter's type, and for a class type that conversion
is the initialization of a temporary of the type ([temp.arg.nontype]/3).
A derived instance passed for a base-typed parameter is therefore sliced
to its base subobject, and the derived value and the base's own value
name one specialization ([temp.type]/1). A reference parameter denotes
the object instead, so two objects are always two specializations;
beman.transpose's `const auto &TC` is one, and it keeps a derived
instance apart from its base. The library's instance types could not
take the by-value form in any case. A constant template parameter of
class type must be structural, with every base public ([temp.param]/12),
and a derivation base keeps the implementation as a protected base.

**A protected base does not hide the implementation.** `derive_functor<Impl>`
inherits `Impl` protected, which reads as keeping it out of view. Implicit
conversion sequences ignore accessibility ([over.best.ics.general]/2), and
deduction from a derived class goes through the protected base, so a
function naming `Impl` is selected, and then the conversion makes the call
ill-formed ([conv.ptr]/3, [dcl.init.ref]/4).

```cpp
struct impl {};
struct derive_impl : protected impl {};
struct map : derive_impl {};

void use(const impl&);
use(map{});   // selected, then ill-formed: impl is an inaccessible base
```

The call is not merely not viable, so no other overload is tried. Inside a
requires-expression the same failure is part of substitution and the
requirement is simply false.

All five come down to the exact-type rule above: inherit if you like, but
never name an instance type, or what it is built from, in a signature.

# Across translation units

Some violations make a program ill-formed with no diagnostic required,
because nothing useful can be said about one entity with two contrary
definitions. The model follows the Standard's lead. It treats a program as
a list of translation units, each resolved on its own, and when units
disagree it gives a verdict, ill-formed with no diagnostic required, naming
the rule and the use, and says nothing more.

A use of a lookup gets a verdict when its selection is not the one it
would make with every instance of the program reachable:

- an instance declared later in the same unit gives the specialization a
  second point of instantiation with a different meaning ([temp.point]/7);
- an instance declared only in another unit is not reachable from a use
  that would make use of it ([temp.spec.partial.general]/1).

For a single unit, having no verdict is exactly the condition that every
instance is declared before every use of its lookup. Stated per unit,
stability at the call surface says a call sees what precedes it: an
instance declared after the call cannot move it, and can only make the
program ill-formed with no diagnostic required.

A free-function design has two more verdicts, and the object design has
neither. A dependent call `fmap(f, t)` in a template is looked up where
the template is defined and again, by argument-dependent lookup, at the
specialization's point of instantiation. A better overload in an
associated namespace that only another unit declares makes the program
ill-formed, no diagnostic required ([temp.dep.candidate]/1). Within one
unit, the specialization has a point of instantiation after each
declaration that refers to it and another at the end of the unit, and an
overload declared between them gives the call two meanings, which is
ill-formed by the rule that makes a late instance so ([temp.point]/1,
/7). GCC and Clang fix the meaning at the first point. When ordinary
lookup binds the name to an object, argument-dependent lookup never
runs, so no unit and no point can add a candidate.

The important result is about identity. One might expect a function whose
behaviour depends on an instance to be safe across units whenever the
instance is one of its template arguments, since units that select
different instances would then have different specializations. The
operation object does take the instance as a template argument, but as a
reference to the lookup variable, `const auto &TC = functor<...>`. A
reference argument is the entity it designates, and `functor<box<int>>`
is one entity in every unit, whatever its initializer selects: its
declarations correspond, inhabit one scope and have external linkage
([basic.link]/8). Two units that select different instances therefore
deduce *one* specialization, and the program gives one function two
meanings, ill-formed with no diagnostic required by [basic.def.odr]/16.
That verdict never comes first: one of the two selections differs from
the whole program's, so a verdict at the lookup is already there.
Pinning names the instance object and does separate the units. The
by-value policy names the instance's type and separates them only when
instances have distinct types.

Being a variable is what makes the operation object immune to
overloading, and what exposes it to the one-definition rule. Visibility
is the obligation that keeps that exposure from mattering.

# Results about dispatch idioms

The model was used to compare idioms a typeclass author is likely to
reach for.

**Mandates.** A Mandate, checked only after selection, never changes which
candidate is selected; it can only turn a selection into an ill-formed
program, with no fallback to another overload. Turning a Mandate into a
constraint does remove the candidate where the Mandate fails. Where it
holds, the larger constraint can change partial ordering:

```cpp
template <class T> requires class_like<T> void g(T);              // #1
template <class T> void g(T) { static_assert(empty_like<T>); }    // #2

g(X{});   // #1, the more constrained; #2's Mandate is never checked
```

Promote #2's Mandate to `requires empty_like<T>`, and neither constraint
subsumes the other: the call becomes ambiguous, an outcome neither the old
resolution nor removing #2 gives. So promotion is not merely removal.

**`enable_if` and requires-clauses.** With the same condition, an
`enable_if` in a trailing return type and a requires-clause give the same
viable set, and the same resolution wherever ordering does not consult
subsumption. They differ in two ways. A requires-clause wins orderings by
subsumption that `enable_if` cannot. And the step order differs: a
requires-clause is checked before the function type is substituted, so it
shields a hard error in a parameter's type, while `enable_if` in the return
type is checked only as that type is substituted, after the parameters:

```cpp
template <class T> requires integral_like<T>
void f(T, std::remove_cvref_t<decltype(lookup<T>)>);                // not viable
template <class T>
auto f(T, std::remove_cvref_t<decltype(lookup<T>)>) -> std::enable_if_t<integral_like<T>>;
                                                                    // hard error
```

where `lookup<T>` fails hard for the argument's type. Substitution follows
lexical order ([temp.deduct.general]/7), so a leading return type would
check `enable_if` first; the result above is specific to the trailing form.

**Dispatch styles.** For an ordered list of conditions, constraint
exclusion, priority tags and an `if constexpr` chain select the same
candidate. With no condition holding, the first two leave the call not
viable and the chain is ill-formed. They also differ in which conditions
are evaluated. The chain stops at the first that holds, and so does
exclusion written with the negations first, since a conjunction is checked
left to right. Priority tags check every overload's condition, because
every overload is a candidate, so a later condition that fails hard breaks
the call. The library's lookups default to `std::false_type`, so its own
conditions cannot fail that way.

# Findings about the Standard and implementations

## The Standard

- [temp.constr.order]/2, a note, says subsumption "defines a partial
  ordering on constraints". It is reflexive and transitive, but `A ∧ B` and
  `B ∧ A` subsume each other and are different constraints, so it is a
  preorder. It is a partial order on constraints taken up to mutual
  subsumption, which is presumably what is meant. Normative text is
  unaffected.

## Implementations {#implementations}

- **An ambiguous instance is treated as no instance.** At a type two
  instances match with neither more specialized, the use of the lookup in
  the operation object's default template argument is ill-formed by
  [temp.spec.partial.match]/1, and since it is an instantiation it is
  outside the immediate context ([temp.deduct.general]/8), so the call is
  ill-formed. GCC 13 to 16 and Clang 17 to 24 instead treat the call as a
  deduction failure and select another overload if there is one. The same
  holds for the by-value route. So canonicity is not checked at the call
  surface in practice: overlapping instances make a type silently look as
  if it had none. The compilers do diagnose the lookup itself.
- **Constraints before the function type.** Clang 17 to 20 substitute the
  function type, and check conversions to non-dependent parameters, before
  checking constraints, the ordering CWG2369 [@CWG2369] replaced. The draft's own
  second example in [temp.deduct.general]/5 fails to compile on them, and
  a requires-clause does not shield a hard error in a parameter's type.
  Clang 21 to 24 and GCC 13 to 16 follow the current text.
- **A perfect non-template match.** GCC skips deduction for template
  candidates when a non-template is an exact match, in some cases, and
  Clang 21 to 24 do so in more, including constraint satisfaction. This is
  the direction of P3606 [@P3606R2]. The two implementations disagree about what it
  covers, which is evidence for what its wording needs to say.
- **Placeholder type-constraints.** [temp.over.link]/6 makes constant
  template parameters equivalent ignoring type-constraints on placeholder
  types, so `auto` and `shape auto` parameters leave the tie-break of
  [temp.func.order]/8 open. Clang 19 to 24 and GCC 16 agree. GCC 13 to 15
  and Clang 17 and 18 report the call ambiguous.
- **A derived value for a base-typed constant parameter.** Under
  [temp.arg.nontype] as rewritten by P2308R1 [@P2308R1], a derived class value is
  accepted for a constant template parameter of base class type, sliced,
  and identified with the equal base value. Clang 17 to 24 do this. GCC
  13 to 16 reject it as not a converted constant expression, the rule
  before P2308R1.

# Limits of the model

The model covers a fragment. Partial ordering is proved transitive for
templates of type parameters whose parameter types have no references; with
references, the tie-breaks of [temp.deduct.partial]/9 enter, and the
evidence is a search over 5832 triples of parameter shapes that found no
counterexample. Deduction is proved sound and most general on the
first-order fragment; references nested in a parameter type have two
solutions under reference collapsing, and deduction gives the one the form
`T&` prescribes. Dispatch styles are compared exhaustively over three
conditions, not proved for every length. The conversion ranking covers
identity, derived-to-base and reference binding; arithmetic conversions,
user-defined conversions and access from inside a class are outside.
Concept satisfaction is an oracle, not a semantics of expressions.
A registry that tests for an instance by completeness, as
beman.transpose's `Monoid` does, is a third encoding. The model covers
only its verdicts: they are a lookup's, at the same uses, under a third
rule where the test's answer changes, a satisfaction result that differs
at two points ([temp.constr.atomic]/3). Name lookup covers namespace
and class scopes, without using-directives, using-declarations, blocks
or modules, and a class is named by its name alone. Member lookup
follows [class.member.lookup] over the fragment's members, with no
explicit object parameters. The member call at an operation object's
constraint is still an oracle: the model takes its answer as a
parameter, and proves only what the operation object and an algorithm
over the instance make of it. Which members are accurate comes from
compiling against beman.transpose, not from the model. Template
arguments are converted for integer and class values, and the draft's
own example of a narrowing argument is a theorem; floating-point,
pointer and enumeration values, user-defined conversions and braced
lists are outside, and a deduced value is not converted, so
[temp.deduct.type]/20 is outside the fragment. The model has one instance per
key, and no copies or object state, so the obligations on an algorithm
to use the instance and the object it was given, and to pass a reference
for identity, rest on probes alone. Function parameter packs are
outside the fragment. Applicative's `invoke` takes one after the argument
that keys the lookup, and the pack does not enter the lookup.

# Implementation experience

The model and the generated tests are in the overload repository. The
Lean sources are under `Overload/`, built with Lean 4.35 and Batteries,
and every result named here is audited to depend on no unproven axiom.
`make differential` emits the 125 C++ programs and compiles each with the
listed compilers; `differential/known-disagreements.txt` lists each case
and compiler where an implementation departs from the text.

The sources have two sides. `Overload/` transcribes the Standard and
proves properties of the rules alone; `Overload/Typeclass/` defines the
encoding on top of it, and nothing on the Standard side imports it. The
main results, by file:

- `Overload/Lookup.lean`: `coherence`, `stability`, for any variable
  template with partial specializations.
- `Overload/Separability.lean`: `separability`.
- `Overload/Erasure.lean`: `inheritance_erasure`.
- `Overload/Access.lean`: `protected_base_selected_ill_formed`,
  `protected_base_deduced_ill_formed`.
- `Overload/Units.lean`: `verdicts_single`, `late_insertion_verdict`,
  `registry_verdicts`, `odr_verdict_implies_verdict`.
- `Overload/Scope.lean`: `corresponds_iff`, `redeclaration_inert`, and
  `sameEntity` with the linkage condition of [basic.link]/8.
- `Overload/Names.lean`, `Overload/Adl.lean`, `Overload/Members.lean`:
  `inner_hides_outer`, `object_suppresses_adl`,
  `free_function_admits_adl`, `derived_member_hides_base`.
- `Overload/DependentCandidate.lean`: `late_adl_overload_verdict`,
  `object_design_no_adl_verdict`, `later_function_verdict`,
  `object_design_one_meaning`.
- `Overload/Arguments.lean` and `Overload/Identity.lean`:
  `convertArg_iff`, `narrowing_constant`, `slicing_identifies`,
  `reference_keeps_identity`.
- `Overload/Mandates.lean`: `mandate_inertness`, `constraint_promotion`,
  `promotion_reorders`.
- `Overload/Sfinae.lean`: `sfinae_requires`, `sfinae_loses_subsumption`,
  `sfinae_unshielded`.
- `Overload/Dispatch.lean`: `dispatch_styles`, `dispatch_hard_condition`.
- `Overload/Conjunction.lean`: `conjunction_answers`,
  `conjunction_no_hard`.
- `Overload/Generality.lean` and `Overload/Transitivity.lean`: soundness
  and generality of deduction, and transitivity of partial ordering.
- `Overload/Typeclass/Encoding.lean`: `fmapObject_deduce`,
  `call_stability`; `Overload/Typeclass/Routes.lean`: the
  explicit-instance routes.
- `Overload/Typeclass/Inheritance.lean`: `rank_beats_refinement`,
  `derived_class_deduction`, `superclass_identity`.
- `Overload/Typeclass/Units.lean`: `operation_object_not_separated`,
  `byValue_separated`, `call_stability_unit`.
- `Overload/Typeclass/Members.lean`: `fmapObject_member`,
  `call_stability_arity`, `arity_order_matters`, `algorithm_transfer`,
  `algorithm_accurate`, `call_order_matters`.
- `Overload/Typeclass/Lookup.lean`: `object_design_candidates`,
  `call_stability_object`, `unconstrained_member_hides_constrained`.
- `Overload/Typeclass/Arguments.lean`: `value_route_slices`,
  `pin_keeps_identity`, `value_route_needs_structural`.

The probes of beman.transpose's own typeclasses, one translation unit
per call, are in `probes/library/`, with their results at the commit
probed in `docs/probes.md`. They include 88 calls of instance members
with the callables a user would pass, and runtime probes of a second
instance for one context, of instance state and of a stateful callable.

The encoding studied is a reduction of beman.transpose
(`github.com/bemanproject/typeclass`), kept faithful to it in
`src/smd/overload/encoding.hpp`.
