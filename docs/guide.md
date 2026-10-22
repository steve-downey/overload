# A guide to the model

What is where, and what it means. This is the map for someone who knows
C++ well and Lean a little, and who wants to find a result and read it
without the decision log or the plan. Decisions are in
[decisions.md](decisions.md), what the work turned up in
[findings.md](findings.md), and the obligations table in
[obligations.md](obligations.md). This document does not repeat them.

## Two sides

The Lean sources are one library, `Overload`, in two layers.

- **The Standard side**, `Overload/*.lean`, namespace `Overload`. Rules
  transcribed from the draft, one cited sentence per constructor or
  definition, and theorems about those rules alone. Nothing here is about
  typeclasses. The examples use neutral names: a variable template is
  `trait<T>`, a class is `X`.
- **The typeclass side**, `Overload/Typeclass/*.lean`, namespace
  `Overload.Typeclass`. The encoding of beman.transpose, defined as
  programs and function templates of the Standard side's syntax, and the
  theorems about it.

The Standard side never imports the typeclass side. `#check_layering` in
`Overload.lean` fails the build if a module of `Overload.*` outside
`Overload.Typeclass` imports one inside it. So a reader of the Standard
side can stop at the directory boundary, and a result named
`Overload.Typeclass.something` is about the encoding and nothing else.

The one place the vocabulary leaks is the program syntax. A variable
template with partial specializations is declared as `Decl.lookup` and its
partial specializations as `Decl.instance`, and the atomic constraint that
asks whether a lookup found a specialization is `has_instance`. Those are
the Standard side's names for a variable template, its partial
specializations and its primary, because that is the use the model was
built for. Read "lookup" as "variable template" and "instance" as "partial
specialization" and every Standard-side statement is about the language.

## How to read the Lean

A few conventions carry the whole development.

- **Syntax is data.** A C++ type is a value of the inductive type `Ty`:
  `.named "int"`, `.param 0` for the first template parameter, `.const`,
  `.ptr`, `.lref`, `.rref`, `.spec "C" args` for `C<args>`. A template
  argument list is spelled inside `Ty` as `.nil` and `.cons`, so every
  proof is an ordinary structural induction; `Ty.spec'` and `Ty.args` give
  the readable spelling. A constant template argument is `.value v`, and
  `.lookup "trait" t` is the variable template specialization `trait<t>`.
- **Two outcome types.** Substitution returns `Subst α`: `.ok a`, `.soft
  reason` for a deduction failure in the immediate context, `.hard reason`
  for an ill-formed program. Resolution returns `Resolution α`: `.selected
  a`, `.noMatch`, `.ambiguous l`, `.illFormed reason`. Every theorem about
  "soft versus hard" is a theorem about which constructor comes out.
- **Each mechanism twice.** A rule is an inductive relation
  (`DeduceTy`, `Selects`, `BetterFunction`, `Resolves`) with one cited
  constructor per sentence, and an executable function (`deduceTy`,
  `select`, `betterFunction`, `resolve`). The theorem named `_iff` says the
  two agree. The relation is what the Standard says; the function is what
  runs, drives the tests, and emits the C++.
- **What the model does not model, an oracle answers.** `Env` has four
  fields: `instantiate` for the value of a variable template
  specialization, `atomic` for whether an atomic constraint's expression is
  valid and true, `convertible` for whether an argument converts to a
  non-dependent parameter, and `bases`. A theorem quantified over `env :
  Env` holds whatever expressions, concepts and classes a program has.
  `Env.ofProgram p` is the environment a concrete program defines.
- **Hypotheses that look like noise are side conditions.** `hf :
  f.ty.isType = true` says an argument's type is a type and not a template
  argument list; `hxF : x.ty.formed = true` says forming it neither
  computes nor instantiates; `hxr : x.ty.isRef = false` says it is not a
  reference. They say the arguments are ordinary, and they are discharged
  by `rfl` for any concrete call.
- **A theorem proved by `rfl` or `decide` is a computation.** Many results
  about a particular shape of program (`rank_beats_refinement`,
  `protected_base_selected_ill_formed`, `arity_order_matters`) are stated
  as equalities on a concrete program and proved by running the model.
  They are theorems in Lean's sense and tests in the engineer's sense.
- **Citations are attributes.** `@[std rule "temp.deduct.general#5.sentence-6"]`
  on a definition says what sentence it transcribes. `@[std theorem ...]`
  says the sentence is proved from the others. `@[std note ...]` and
  `@[std example ...]` are non-normative text used as proof targets.
  `@[assumed "slug"]` marks something the Standard does not say, linked
  to a section of [decisions.md](decisions.md). `#check_citations` fails
  the build when a constructor of a `@[specification]` relation is
  uncited, and `#audit name` fails it when a theorem rests on anything
  but Lean's three standard axioms and tagged assumptions. A `sorry` is an
  axiom, so there are none.
- **Tests are `#guard`.** `OverloadTest/*.lean` evaluates the executable
  side on the draft's own examples and on the probes, and `lake test`
  fails if any guard is false.

## The Standard side, module by module

In dependency order. Each entry says what the module models, which
sentences it transcribes, and what its theorems say in C++ terms.

### Std and Lint

`Overload/Std.lean` defines the `std` and `assumed` attributes, the draft
pin (`draftPin`, N5054), and the list of in-scope paragraphs (`inScope`)
that the citation index checks for coverage. `Overload/Lint.lean` is the
three lints: `#check_citations`, `#audit`, `#check_layering`.

### Syntax

`Overload/Syntax.lean`: `Ty`, `Val` for constant template argument
values, substitution of bindings into a type (`Ty.subst`), and
template-argument equivalence. `Val.Equivalent` transcribes [temp.type]/2
and `Val.equivalent_iff` says it is structural equality on the values the
fragment has. Constant arguments are structural values, trees with
decidable equality, and that equality is the model's notion of two
template arguments being the same.

### Outcome

`Overload/Outcome.lean`: `Subst` and `Resolution`. `hard_absorbing` is the
one fact that matters: once a step fails hard, nothing later can rescue
the substitution. Every step-order theorem is this lemma applied to a
particular step.

### Deduction

`Overload/Deduction.lean` transcribes [temp.deduct.type]: deduction of one
`P`/`A` pair against bindings so far, as the relation `DeduceTy` and the
function `deduceTy`. `deduceTy_iff` is the agreement theorem.
`deduceTy_det` proves [temp.deduct.type]/2 sentence 3, that the pairs are
deduced independently and a conflict is a failure, from the other rules:
the same `P`, `A` and starting bindings always give the same answer. The
call-site adjustments of [temp.deduct.call]/2 and /3 (`adjustA`,
`adjustP`, the forwarding-reference rule) and deduction from a derived
class ([temp.deduct.call]/4 and /5, `deduceFromBase`) make `deduceCall`:
every parameter of a function template against the arguments of a call.

### Generality

`Overload/Generality.lean` is the exit criterion for deduction. On the
first-order fragment, types without references nested inside them,
deduction is matching. `deduceTy_subst`: substituting the bindings it
returns into `P` gives `A`. `deduceTy_most_general`: any bindings that
make `P` equal a non-dependent `A` extend the ones deduction found. Both
are tagged as theorems of [temp.deduct.type]/1 sentence 1, "find template
argument values that will make P, after substitution, compatible with
A". Reference collapsing breaks uniqueness, which is why the fragment
excludes references inside `P`; a call strips the top-level reference
before deducing, so this covers `T`, `const T&`, `T&&` and `C<T>*`.

### Constraint

`Overload/Constraint.lean`: constraints as `atomic`, `conj`, `disj`;
satisfaction ([temp.constr.atomic]/3) as left-to-right evaluation that
treats an invalid substitution as not satisfied; and subsumption
([temp.constr.order]/1) by disjunctive and conjunctive normal form with
atomic identity ([temp.constr.atomic]/2).

The results are the whole of what the Standard's ordering of constraints
amounts to on this fragment.

- `subsumes_iff`: `P` subsumes `Q` exactly when `P` implies `Q` as a
  propositional formula with the atomic constraints read as free
  variables. Subsumption is implication that cannot see inside an atom.
- `subsumes_refl`, `subsumes_trans`: a preorder.
- `subsumes_not_antisymm`: not a partial order. `A ∧ B` and `B ∧ A`
  subsume each other and are different constraints. This refutes the note
  in [temp.constr.order]/2 as worded; see
  [findings.md](findings.md#against-the-standard) and
  [the issue draft](../papers/subsumption-partial-ordering-issue.md).
- `subsumes_satisfied`: if `P` subsumes `Q` and `P` is satisfied, then `Q`
  is satisfied or checking `Q` is a hard error. `subsumes_satisfied_hard`
  shows the hard error happens: `A` subsumes `B ∨ A`, and checking `B ∨ A`
  evaluates `B`, which checking `A` never touched.
- `satisfaction_implication_not_subsumes`: the converse fails, because two
  different atomic constraints can mean the same thing.
- `moreConstrained_asymm`, `moreConstrained_trans` (the latter in
  `Transitivity`): "more constrained" is a strict partial order.

### Program

`Overload/Program.lean`: programs as ordered lists of declarations,
`Decl`: classes with public and protected bases, class templates,
functions, function templates (`FunctionTemplate`: head, parameter types,
default arguments, return type, associated constraint, Mandates), a
variable template as `lookup` or `lookupHard` (a primary with a value, or
one whose instantiation fails), its partial specializations as `instance`,
a use of it, an object, a concept. Each namespace-scope declaration
carries the scope it inhabits, a path of namespace and class steps from
the global scope inward, `[]` by default (`decisions.md#scope-syntax`).
`Program.candidates` is every declaration with a name, in order; `Scope`
reduces it to the overload set, one declaration per entity, and `Names`
computes what a call finds from a program point and a scope.
`SingleTranslationUnit` is the one tagged assumption of the development:
every partial specialization is declared before any use of its variable
template. `Units` removes it.

### Arguments

`Overload/Arguments.lean`: the conversion of a constant template argument
to its parameter's type ([temp.arg.nontype]). `integerTypes` is the
fragment's integer types with their ranges under LP64
(`decisions.md#integer-widths`), `representable` whether a type holds a
value, `literalType` the type of an integer literal ([lex.icon]/3), and
`Val.sourceType` the type a value's source expression has, since a value
carries none (`decisions.md#value-typing`). `Narrowing` and `narrowing`
are [dcl.init.list]/7 as relation and function (`narrowing_iff`), and
`narrowing_constant` says that for a constant source the two halves of
the rule collapse: narrowing is exactly the value not being representable
in the target. `convertedConstant` is the converted constant expression
of [temp.arg.nontype]/2 on the fragment's values, admitting promotion and
non-narrowing integral conversion ([expr.const.const]/8). `ConvertsTo`
and `convertArg` (`convertArg_iff`) convert an argument against a
parameter of either kind: a type; a placeholder, which takes the argument
as its own type; a dependent declared type, formed later; an integer
type; a class type, whose value is the argument's or the base subobject
of a derived value, through the environment's `subobject` oracle; an
lvalue reference, which binds an object and refuses a temporary
([temp.arg.nontype]/6). The conversion never fails hard
(`convertArg_not_hard`), and two oracles that agree on the value give one
conversion (`convertArg_congr`). `tpo_value` is [temp.arg.nontype]/4 on
a fragment where equivalence is equality.

### Steps

`Overload/Steps.lean` is [temp.deduct.general]/5 as seven functions
composed with `>>=` on `Subst`, one per sentence, so the first failure
stands: explicit arguments, deduction from the call, defaults,
the parameter list, constraints, convertibility of non-dependent
parameters, the function type. `form` is [temp.deduct.general]/8: forming
a type in the immediate context, where an invalid type is a soft failure
and instantiating a variable template specialization asks the environment
and may fail hard. `deduceTemplate` is the whole of deduction for a
function template. The explicit step converts each argument against its
parameter's declared type, substituted with the preceding explicit
arguments ([temp.names]/13), and the defaults step converts a constant
parameter's default; a conversion that fails is soft and is the outcome
(`conversion_soft_shields_call`, `explicitStep_not_hard`), and two
arguments with one converted value give one bindings list
(`explicitStep_converted`). `Env` carries one oracle for it,
`subobject`, the base class subobject of a class value, which
`Env.ofProgram` computes from the program's classes
(`Program.subobject`, in `Ranking`).

The theorems say what the order buys.

- `defaults_hard_absorbing`: a hard error while substituting a default
  template argument is the outcome. Nothing later is reached.
- `constraint_cannot_guard_default`: a requires-clause on the same
  template cannot protect its default, because defaults come first. This
  is the step-order hazard: a defaulted constant parameter whose default
  instantiates something that fails hard makes every call that deduces
  the template ill-formed, whatever the constraint says.
- `constraint_soft_shields_function_type`: a constraint that is not
  satisfied stops the function type from being substituted. This is what
  keeps the draft's own second example in [temp.deduct.general]/5
  well-formed, and what Clang 17 to 20 got wrong.
- `deduceTemplate_hard_iff`: deduction fails hard only where a step did,
  after every earlier step succeeded.

The module ends with lemmas about the steps on the shapes a call presents
(`Ty.formed`, `forwarded`, what an `ok` step says about its bindings),
which both sides use.

### Identity

`Overload/Identity.lean`: what names a specialization.
`sameSpecialization` is [temp.type]/1 through the explicit step: two
argument lists name one specialization when the parameter values they
determine are the same. `slicing_identifies`: under a base-typed class
value parameter a derived value and the base's own value are one
specialization, since the derived value is sliced to its base subobject.
`reference_keeps_identity`: under a reference parameter two objects
never are, since the parameter denotes the object ([temp.type]/2).
`Program.structural` is [temp.param]/12, and
`placeholderArgumentsPermitted` the check of [temp.arg.nontype]/1 that a
class value a placeholder parameter takes has a structural type, at the
program level, where the class declarations are. The draft's narrowing
example, [temp.deduct.general]/12, is `temp_deduct_general_12_example`
in `Access`, at the level of a call: `f<1000>` selects the `int`
template and `f<1>` is ambiguous.

### Ordering

`Overload/Ordering.lean`: partial ordering of function templates
([temp.func.order], [temp.deduct.partial]) and partial specialization
matching ([temp.spec.partial.match], [temp.spec.partial.order]).

`transform` synthesizes a unique type (`Ty.synth`) or value for each
template parameter. `atLeastAsSpecialized` deduces one template's
parameter types from the other's transformed ones, with the reference
tie-breaks of [temp.deduct.partial]/9 (`denies`). `moreSpecialized` is
"at least as specialized and not conversely", and when each is at least
as specialized as the other, the constraints decide, but only through the
gate of [temp.func.order]/8: same-length parameter lists, equivalent
template parameters ([temp.over.link]/6, `paramEquivalent`, which ignores
a type-constraint on a placeholder), same function parameter types.
`tieBreak_needs_equal_heads` proves that gate from the rest. The sentence
is tagged as a theorem, which means the draft could say less there.

`moreSpecialized_irrefl` and `moreSpecialized_asymm` are what a strict
partial order needs besides transitivity, which is in `Transitivity`.

Partial specialization matching rewrites each partial specialization to a
function template with one parameter ([temp.spec.partial.order]/1,
`rewrite`) and orders those. `patternMatches` is deduction of the pattern
against the argument, `PatternMatches` the relation, `patternMatches_iff`
their agreement, which makes matching deterministic because deduction is.
`select` picks among a list of partial specializations: the primary, the
unique match, the most specialized match, or ambiguity. `Selects` is the
relation, one constructor per case of [temp.spec.partial.match]/1;
`select_iff` is the agreement; `mostSpecialized_unique` says at most one
match is most specialized.

### Transitivity

`Overload/Transitivity.lean`: `moreSpecialized_trans`, tagged as a
theorem of [temp.func.order]/2 sentence 4. It is proved for templates of
type parameters whose parameter types have no reference, with any number
of parameters. The gate and more-constrained are transitive outright. At
least as specialized is transitive because on the fragment deduction is
matching and a match against synthesized types lifts to every
substitution. References bring in the tie-breaks of
[temp.deduct.partial]/9; there the evidence is the search in
`OverloadTest/Ordering.lean` over 5832 triples of parameter shapes, with
no counterexample found.

### Specs

`Overload/Specs.lean`: the relation forms of ordering and resolution,
built on `DeduceTy`, with agreement theorems: `DeducePairs`,
`AtLeastAsSpecialized`, `MoreSpecialized`, `BetterFunction`, `BestViable`,
`Resolves`. Each `_iff` says the function computes exactly the relation.
The point is that `resolve` is not an implementation that happens to
agree with some tests; it is proved to be the transcription.

### Resolution

`Overload/Resolution.lean`: the call surface. `generate` is
[over.match.funcs.general]/8, each function template contributing the
specialization its deduction produces or nothing on a soft failure, with
a hard failure in any candidate the outcome of the whole call. `viable` is
[over.match.viable]: arity with default arguments and an implicit
conversion sequence per argument. `betterFunction` and `bestViable` are
[over.match.best.general]/2 and /3: conversion sequences first, then a
non-template over a template specialization, then partial ordering.
`resolve` composes them.

`Ranking Conv` is the conversion ranking as a parameter: which conversion
sequences exist and which is better. Every core theorem quantifies over
it. `identityRanking` is the trivial one.

`Mode` is the P3606 switch. Under `.text`, the C++26 text, every template
candidate is deduced. Under `.p3606` a non-template candidate that is a
perfect match (`perfectMatch`, the model's reading of unsettled wording)
suppresses deduction for the templates. `generate_agree_of_no_perfect`,
`generate_p3606_suppresses` and `generate_differ_implies_perfect` say the
two modes differ exactly when a perfect match exists, and then only in
that the templates are never deduced. `resolve_congr` says resolution
depends on the environment only through deduction, and
`resolve_text_hard` that under the text a hard deduction failure of any
candidate is the call's outcome.

### Ranking

`Overload/Ranking.lean`: the one concrete ranking, `Program.ranking`,
over class hierarchies: the identity conversion, derived-to-base
([over.best.ics.general]/7, Conversion rank), direct reference binding
([over.ics.ref]), and the tiers of [over.ics.rank]/3 as a lexicographic
chain. `better_iff` is the agreement with the relation `BetterConv`;
`better_asymm`, tagged as a theorem of [over.ics.rank]/1, says the
ordering is asymmetric for any class hierarchy. `Program.ics` is the
convertibility the environment uses for non-dependent parameters, so
deduction and ranking agree on what converts.

### Lookup

`Overload/Lookup.lean`: a variable template over a program.
`Program.instancesOf` collects its partial specializations in declaration
order; `Program.selectInstance` is `select` over them.

- `coherence`: lookup selects a partial specialization exactly when it is
  the most specialized match, and by `mostSpecialized_unique` at most one
  is. `coherence_ambiguous` and `selectInstance_ne_illFormed` cover the
  other outcomes: the primary, or a reported ambiguity, never a silent
  choice.
- `stability`: declaring one more partial specialization, anywhere in the
  program, leaves lookup unchanged at every type the new one does not
  match, and at a type it does match the lookup keeps its answer, moves to
  the new specialization, or becomes ambiguous. `stability_other_typeclass`
  says another variable template's lookup does not move at all.

Neither theorem needs a single translation unit or a soft primary. They
are about matching, and they hold for `std::formatter`-style
specialization as much as for a typeclass instance.

### Environment

`Overload/Environment.lean`: `Env.ofProgram p atomics extra`, the
environment a program defines. Instantiating `trait<a>` is lookup: a
selected partial specialization has a value (named by the type
`instance_of<a, i>`), an ambiguous lookup is a hard error, since matching
partial specializations is part of instantiation and so outside the
immediate context, and a primary either has a value or fails. The atomic
constraints `has_instance` and `lookup_formed` are answered from the same
selection; others from the case's table of ground truths, and failing
that from `extra`, which is how the typeclass side adds constraints whose
meaning is its own without the Standard side knowing them.

### Separability

`Overload/Separability.lean`: `separability`. Two rankings, of any
conversion types, that both select a candidate at the same position select
the same candidate, with the same specialization and so the same template
arguments. The ranking chooses among candidates and never changes what a
candidate is, because candidates are generated, and their template
arguments deduced and converted, before any conversion sequence is
ranked. One lemma per suspect the plan named: a hard error in generation
is the outcome under every ranking (`separability_step_order`); a
selected specialization is what deduction produced
(`separability_argument_identity`); every selected candidate is a
generated one (`separability_argument_conversion`); with equal conversion
sequences the ranking drops out (`separability_tie_break_reach`); a worse
conversion for any argument loses whatever the non-template preference
and partial ordering say (`separability_rank_precedence`). `ranking_live`
is the reminder that the ranking still decides which candidate wins.

### Erasure

`Overload/Erasure.lean`: `inheritance_erasure`. Erasing the base classes
of a set of classes (`Program.eraseBases`) changes no call in which every
conversion the call can form has the same class on both sides whenever
either side is a class the erasure touches (`ExactPair`), and no argument
of a touched class is deduced from as a derived class
(`NoDerivedDeduction`). The hypothesis is about conversions rather than
signatures because a template parameter deduced from one argument can
meet another argument of a derived type. `deduceTemplate_congr`, on the
way, says deduction depends on the environment only through
instantiation, atomic answers, bases and convertibility.

### Mandates

`Overload/Mandates.lean`: a Mandate as a condition checked only after
selection, when the selected specialization's definition is instantiated
([structure.specifications]/3). `invoke` is resolution then the Mandates.

- `mandate_inertness`: adding a Mandate to a candidate never changes which
  candidate is selected. `invoke_selected`: it can only turn a selection
  into an ill-formed program.
- `constraint_promotion`: turning a Mandate into a constraint removes the
  candidate where the Mandate fails, so the call resolves as if the
  declaration were absent. Where the Mandate holds the candidate stays,
  but its constraint has grown, so partial ordering can change.
  `promotion_reorders` is the counterexample: a template that lost to a
  more constrained sibling ties with it after promotion, and the call
  becomes ambiguous.

The proofs go through a relabelling argument (`ContribRel`, `Keeps`):
resolution cannot see a change to a candidate that keeps what resolution
reads. The same machinery serves `Sfinae`.

### Sfinae

`Overload/Sfinae.lean`: a requires-clause against `enable_if` in a
trailing return type, with the same condition. `sfinae_requires`: the same
viable set, provided the condition, the convertibility check and the
function type never fail hard. `sfinae_requires_resolve`: the same
resolution where partial ordering does not change. Where they differ:
`sfinae_loses_subsumption`, the `enable_if` form has no constraint for
subsumption to compare, so a call the requires-clause wins is ambiguous;
`sfinae_unshielded`, `enable_if` is checked while the function type is
substituted, after the parameters, so a hard error in a parameter's type
is reached that a requires-clause would have shielded.

### Dispatch

`Overload/Dispatch.lean`: the three ways to pick the first condition that
holds among overloads. Constraint exclusion (`(!c0) && (!c1) && c2`),
priority tags (`rank<N>` parameters), and an `if constexpr` chain.
`dispatch_styles`, checked over the eight valuations of three conditions,
says all three select the first condition that holds, and that with none
holding, exclusion and tags leave the call not viable while the chain is
ill-formed. `dispatch_hard_condition` is the difference nobody expected:
priority tags check every overload's condition, because each overload is a
candidate, so a later condition that fails hard when checked makes the
tagged call ill-formed where exclusion and the chain never look at it.

### Units

`Overload/Units.lean`: a program as a list of translation units, each
resolved alone. `IllFormedNdr` is the fourth outcome, ill-formed with no
diagnostic required, a verdict about the program at a use of a variable
template: a partial specialization declared later in the use's unit would
be selected at the end of the unit ([temp.point]/7, `laterInUnit`); one
declared only in another unit is not reachable ([temp.spec.partial.general]/1,
`notReachable`); a completeness test's answer differs between two points
([temp.constr.atomic]/3, `satisfactionChanged`). `Units.verdicts` lists
them. The model says nothing about a program with a verdict, which is the
honest reading of "no diagnostic required".

- `verdicts_single`: for one unit, the `SingleTranslationUnit`
  assumption is exactly what keeps every use free of a verdict.
- `missing_instance_verdict`, `late_instance_verdict`: the two verdicts on
  two-line programs.
- `callAt`, `callAt_insert_after`: a call sees the declarations before
  it, so a partial specialization declared after a call leaves the call
  as it was. `late_insertion_verdict`: it leaves the use free of a verdict
  or gives it the one of [temp.point]/7, and nothing else.
- A registry tested by completeness, a class template declared and never
  defined whose specializations are the entries and whose uses are
  `requires { Registry<V>{}; }`, has exactly the verdicts of a lookup at
  the same uses (`registry_verdicts`), under the third rule where the
  test's answer changes, and none for one unit
  (`registry_verdicts_single`).
- The one-definition rule's verdict at a lookup, `odrMismatch`: two
  units that instantiate `tc<a>` and select different partial
  specializations define one definable item differently
  ([basic.def.odr]/16, `Units.odrVerdicts`). It never comes first: a
  program with one already has a verdict of [temp.point]/7 or
  [temp.spec.partial.general]/1, since one of the two selections differs
  from the whole program's (`odr_verdict_implies_verdict`,
  `odr_mismatch_example`). This is the rule behind the encoding's
  `operation_object_not_separated`.

### DependentCandidate

`Overload/DependentCandidate.lean`: dependent calls and the fourth
verdict. `Decl.dependentCall` is a call written in a template defined at
its position and instantiated with the arguments it carries, and
`Decl.refersTo` is a namespace-scope declaration that refers to that
specialization. The specialization's points of instantiation are the
point after each referring declaration and the unit's end, each once
([temp.point]/1, /7; `Program.instantiationPoints`), and its point of
instantiation is the first of them. The call's name is looked up from
where it appears, unqualified lookup and argument-dependent lookup, and
argument-dependent lookup runs again from the instantiation context,
which holds that point ([temp.res.general]/1, [basic.lookup.argdep]/4,
[module.context]/5; `Program.dependentLookupAt`,
`Program.dependentLookup`, `Program.dependentCandidates`,
`Program.dependentCallAt`). Two verdicts. The one of
[temp.dep.candidate]/1, `IllFormedNdr.dependentCandidate`: the call
resolves differently over what its two contexts find and over that with
every other unit's associated-namespace functions as well
(`dependentVerdict`, `Units.dependentVerdicts`). The one of
[temp.point]/7, `IllFormedNdr.laterCandidate`: the call resolves
differently at two of its points of instantiation, which give the
specialization different meanings (`pointVerdict`,
`Units.pointVerdicts`). `Units.allVerdicts` lists both with phase 8's
three.

- `dependentVerdicts_single`: one unit, no verdict.
- `object_design_no_adl_verdict`: a callee bound to anything but a
  function, the operation object for one, cannot get the verdict in any
  program, since argument-dependent lookup never applies to it. The
  free-function design can (`late_adl_overload_verdict`): a better
  overload in an associated namespace of another unit, which neither
  context sees, is the verdict.
- `temp_res_general_1_example`: the draft's example, `f(t)` instantiated
  at a type declared after the template, finds the later `f(E)` through
  the instantiation context and selects it. The referring declaration
  `h` is the last, so the specialization has one point.
- `later_function_verdict`: the same declarations with `h` before
  `void f(E);`. The specialization has two points, after `h` and at the
  unit's end; at the first only `f(char)` is found and the call is not
  viable, at the end `f(E)` is selected, and the program has the verdict
  of [temp.point]/7. `pointVerdict_unreferenced`: with no referring
  declaration there is one point, the unit's end, so every program
  without one reads as it did. `object_design_one_meaning`: a callee
  bound to an object has one meaning at every point, since
  argument-dependent lookup never applies to it.

### Access

`Overload/Access.lean`: `Program.call`, a call as a program evaluates it
in an environment: overload resolution, which ignores access
([over.best.ics.general]/2), then the access check on the selected
function's conversions ([conv.ptr]/3, [dcl.init.ref]/4), then the
Mandates. `call_eq_invoke`: when the conversions are accessible, access
changes nothing. `protected_base_selected_ill_formed` and
`protected_base_deduced_ill_formed`: a function that names a protected
base, or a template that deduces through one, is selected and the call is
ill-formed. A protected base is not a way to hide an overload.

### Conjunction

`Overload/Conjunction.lean`: a constraint written as a conjunction of
atomic constraints in order. `satisfied_conjunctionOf`, tagged as a
theorem of [temp.constr.op]/2 sentence 3, says satisfaction reads the
answers left to right and stops at the first that is not valid and true.
`conjunction_answers`: the constraint step passes when every answer is
valid and true, and otherwise the first that is not decides; a hard error
in a conjunct that is never reached does not count. `conjunction_no_hard`:
no hard conjunct, no hard conjunction. A guard belongs before the thing
it guards.

### Scope

`Overload/Scope.lean`: which declarations are one entity. `corresponds`
transcribes [basic.scope.scope]/4: two declarations correspond when they
introduce the same name, unless one declares a type and the other a
variable or function, or each is a function or function template and
they are not corresponding overloads, functions with the same
parameter-type-list or function templates with equivalent heads (the
equivalence of [temp.over.link]/6 that the tie-break gate uses),
parameter lists and return types. `Corresponds` is the relation,
`corresponds_iff` the agreement. `potentiallyConflict` and
`Program.conflicts` are /6: corresponding declarations of different kinds
of entity under one name, such as an object and a function both named
`fmap`, make the program ill-formed (`scopesWellFormed_iff`). Two
declarations declare the same entity when they correspond, inhabit the
same scope, both have external linkage and declare the same kind of
entity (`sameEntity`, [basic.link]/8 and /11); every name of the
fragment has external linkage (`Decl.linkage`, /3 to /5), so the lookup
variable template and the operation object are one entity in every
unit.

`entities` keeps one declaration per entity, the first, since a later
corresponding declaration is a redeclaration ([basic.lookup.general]/1),
and `Program.overloadSet` is the candidates reduced that way. No two
members correspond (`overloadSet_pairwise`); without a corresponding
pair the overload set is the candidate list (`overloadSet_eq_candidates`);
and a redeclaration after its entity's first declaration changes no
call (`redeclaration_inert`, `redeclaration_inert_resolve`,
`redeclaration_inert_invoke`). `candidates_redeclaration_ambiguous` is
what the candidate list got wrong before this module
([findings.md](findings.md#about-the-model)). The emitter computes call
expectations over the overload set.

### Names

`Overload/Names.lean`: name lookup for the fragment, namespace and class
scopes without using-directives, blocks or modules. A program point is a
position in the unit's declaration list, and a declaration precedes it
when it is earlier (`follows`, `precedes`, [basic.lookup.general]/2). A
single search in a scope for a name from a point finds the declarations
before the point that bind the name there (`singleSearch`,
`SingleSearch`, `singleSearch_iff`, /3). An unqualified search is the
single search in the scope, or, finding nothing, the unqualified search
in the parent (`unqualifiedSearch`, `UnqualifiedSearch`,
`unqualifiedSearch_iff`, [basic.lookup.unqual]/2), and unqualified name
lookup from a point is that search in the point's immediate scope
(`unqualifiedLookup`, /3). What lookup found is classified by
[basic.lookup.general]/1 after classes are discarded when anything else
was found (`LookupResult`, `lookupResult`, `discardTypes`): nothing, an
overload set with one declaration per entity, one entity, or ambiguous.

- `inner_hides_outer`: when the immediate scope binds the name, the
  search is the single search there, whatever every enclosing scope
  declares and whatever the signatures. `hiding_example` is the concrete
  shape: `void f(int);` outside and `void f(X);` in `user` leave a call
  `f(1)` written in `user` not viable.
- `unqualifiedSearch_scope`: everything found inhabits one enclosing
  scope.
- `singleSearch_global_eq_candidates`: a single search in the global
  scope over a unit whose declarations of the name are all functions
  there is the candidate list.

### Adl

`Overload/Adl.lean`: argument-dependent lookup and the call from a
point. The associated entities of an argument type are, for a class,
the class and its bases, for a class template specialization the
specialization and the entities of its type template arguments, and
through cv-qualification, pointers and references those of the referenced
type; a fundamental type has none (`Program.associatedEntities`,
`AssociatedEntity`, `associatedEntities_iff`, [basic.lookup.argdep]/3).
The associated namespaces are their innermost enclosing namespaces
(`Program.associatedNamespaces`, /4). The lookup finds every function
and function template declaration of the name a search in an associated
namespace finds (`Program.adl`, `Adl`, `adl_iff`), and it applies when
unqualified lookup found no class member and nothing that is not a
function (`adlApplies`, /1). `Program.callLookup` is unqualified lookup
plus that, and `Program.callAt` resolves a call from a point in a scope
over what it found ([over.call.func]/3). The fragment names a class by
its name alone, so two classes of one name in different namespaces are
outside it.

- `object_suppresses_adl`: a name that unqualified lookup binds to
  anything but a function suppresses argument-dependent lookup, so an
  object named like the callee is the whole of what lookup finds,
  whatever the associated namespaces declare. This is the rule the
  typeclass encoding's operation objects rest on, stated in
  `obligations.md` as "a variable cannot be overloaded".
- `adl_functions`, `adl_scope`: argument-dependent lookup adds only
  functions and function templates, only from associated namespaces.
- `callAt_eq_call_global`: with every declaration of the name a function
  at global scope, a call from the end of the unit is the call over the
  candidate list's overload set, which is why no earlier case moved.
- `argdep_1_example`: the draft's example, `f(s)` finding `N::f` through
  the argument's namespace. `free_function_admits_adl`: with the
  operation a function template, a user's `fmap(X)` beside the user's
  class is found and wins; with it an object, lookup finds the object and
  nothing else. `hiding_call_example`: what the hiding cases select.

The call from a point is in `Members`, once a call on an object has its
candidates.

### Members

`Overload/Members.lean`: member name lookup and the call on an object. A
search in a class scope is the lookup set of [class.member.lookup]/2 to
/5: the class's own declaration set when it is not empty (/3,
`Program.declarationSet`), otherwise the lookup sets of the direct bases
merged in turn (/4, `Program.lookupSet`) by the rule of /5
(`LookupSet.merge`): a set found in a base subobject of one already found
is hidden, differing declarations from unrelated subobjects make the set
invalid, and the same declarations in several subobjects are shared. A
subobject is the path of classes from the class searched down to it. The
result is the declaration set, or ill-formed when invalid (/6,
`Program.memberSearch`). `LookupSetRel` with `MergeBases` is the
relation, `lookupSet_iff` the agreement. A call on an object of class
type resolves over the function call operators of its class, a search
for `operator()` in its scope ([over.call.object]/1,
`Program.callOperators`); every call operator the fragment has is a const
member of one class, so the implicit object parameter is left out.
`Program.callCandidates` and `Program.callAt` are the call from a point:
the overload set lookup found, or the call operators of the object it
found, resolved as `Program.call` does; `Program.memberCallAt` is a
member call `obj.f(args)`.

- `derived_member_hides_base`: a class that declares the name is the
  whole result, whatever every base declares and whatever the
  signatures. `hiding_member_example` is the concrete shape.
- `ambiguous_bases_example`: the example of [class.member.lookup]/6 with
  two unrelated bases, invalid.
- `object_call_candidates`: a callee bound to an object resolves over its
  class's call operators and nothing else.
- `deduceTemplate_at`, `resolve_at_single`: deduction and resolution read
  a template's head, parameters, return type and constraint, never its
  name or scope, so a result about a function template is a result about
  the same template as the `operator()` of a class
  (`FunctionTemplate.at`).
- `callAt_eq_call_global`: with every declaration of the name a function
  at global scope, a call from the end of the unit is the call over the
  candidate list's overload set, which is why no earlier case moved.
- `argdep_1_example`, `hiding_call_example`, `free_function_admits_adl`:
  the examples on programs. The last is the contrast the encoding rests
  on: an operation written as a function template admits a user's
  function of the same name beside the user's class, and it wins; written
  as an object, the user's function is never a candidate.

### Emit

`Overload/Emit.lean`: the C++ emitter. Each declaration is rendered in
its namespaces, the members of a class in its body as const member
functions, a class or class template declared in a namespace is named by
its qualified name wherever a type mentions it, a call case carries the
scope it is written in, and the functions the call resolves over are
numbered by entity in the lookup's order; a declaration of the callee's
name lookup does not find gets a `hidden<j>` return type. A
`memberCall` query is `obj.f(args)` on an object of a class, and a
`dependentCall` query instantiates the dependent call declared at a
position, rendered as a template whose trailing return type names the
call, so the function selected is observable and a lookup failure is a
substitution failure. A `Case` is a program, a query
(deduction, call, lookup, or raw C++) and the expected outcome. `render`
writes a translation unit whose `static_assert`s check the outcome in
unevaluated contexts; a case carries its own `prelude` of fixtures beyond
the common ones. `cases` are the Standard side's, and `computed`,
`computedCall`, `computedLookup` are what the model says, which the tests
compare with what each case states. `scripts/differential.sh` compiles
every emitted unit with every compiler and reports where one disagrees
with the model.

## What the Standard side established

The plan allowed for a fourth outcome: a place where a well-understood
part of the language behaves differently once constant template
parameters carry instances, which would show up as a failed proof. It did
not happen. On the fragment the model covers, every selection mechanism
is deterministic, the orders the Standard calls orders are orders, and
nothing a constant parameter carries reaches past where the text says it
reaches. In detail:

- **Every rule has one reading.** Each mechanism is a relation with a
  constructor per sentence and a function proved to agree with it
  (`deduceTy_iff`, `select_iff`, `patternMatches_iff`,
  `atLeastAsSpecialized_iff`, `moreSpecialized_iff`, `betterFunction_iff`,
  `bestViable_iff`, `resolve_iff`). A conflict between two rules would
  have made a relation non-functional and an agreement theorem false. No
  gap was found: no in-scope input where no rule applies and the function
  had to invent an answer.
- **Determinism** is a theorem at every level: `deduceTy_det` for a pair,
  `patternMatches_iff` for matching, `Selects.det` for selection, the
  agreement theorems for ordering and resolution.
- **More specialized is a strict partial order**: irreflexive and
  asymmetric by theorem, transitive by theorem on templates of type
  parameters whose parameter types have no reference, and by exhaustive
  search over 5832 triples of shapes with references.
- **Subsumption is a preorder, not a partial order**, and it implies
  satisfaction only up to hard errors. The note in [temp.constr.order]/2
  says "partial ordering"; the proof says preorder. Normative text is
  unaffected, since every use asks for one direction.
- **Separability holds with no hypothesis on the ranking.** The
  conversion ranking never reaches a template argument.
- **Six normative sentences are theorems of the others**, tagged
  `@[std theorem]`: [temp.deduct.type]/1 sentence 1 (deduction finds the
  arguments that make `P` compatible with `A`, as soundness and
  generality), [temp.deduct.type]/2 sentence 3 (determinism),
  [temp.func.order]/2 sentence 4 (transitivity), [temp.func.order]/8 (the
  gate), [over.ics.rank]/1 sentence 1 (asymmetry of the ranking),
  [temp.constr.op]/2 sentence 3 (short-circuit of a conjunction). These are
  redundancies, benign, and they say which sentences carry the weight.
- **Name lookup is in the model, and the lookup claims are theorems.**
  The candidate set of a call is computed from a program point and a
  scope: unqualified lookup stops at the first enclosing scope that binds
  the name (`inner_hides_outer`), argument-dependent lookup adds
  functions of the associated namespaces and is suppressed by a name
  bound to anything else (`object_suppresses_adl`), a class's own
  members hide every base member of the name
  (`derived_member_hides_base`), a call on an object resolves over its
  class's call operators (`object_call_candidates`), and a redeclaration
  is not an overload (`redeclaration_inert`), which the candidate list
  had got wrong. Each mechanism is relation and function with its
  agreement (`singleSearch_iff`, `unqualifiedSearch_iff`,
  `associatedEntities_iff`, `adl_iff`, `lookupSet_iff`,
  `corresponds_iff`). Two more verdicts join phase 8's: a dependent call
  that misses a better overload another unit declares
  ([temp.dep.candidate]/1), and a lookup two units instantiate
  differently ([basic.def.odr]/16), which never comes first
  (`odr_verdict_implies_verdict`).
- **Template arguments are converted, and the converted values name the
  specialization.** An explicit or default constant argument is converted
  to its parameter's type by the rules of [temp.arg.nontype], given as
  relation and function (`convertArg_iff`), and the conversion never
  fails hard: a failed one is a deduction failure before any later step
  (`conversion_soft_shields_call`). For a constant, narrowing is
  representability (`narrowing_constant`). The draft's own example,
  `f<1000>` against `template <signed char>`, is a theorem
  (`temp_deduct_general_12_example`) and an emitted case. A derived class
  value under a base-typed parameter is sliced and identified with the
  base's value (`slicing_identifies`); a reference parameter keeps the
  object's identity (`reference_keeps_identity`).
- **Every in-scope paragraph has a counterpart.** The last to get one
  was [temp.point]/1, the point of instantiation after the declaration
  that refers to a specialization (`Decl.refersTo`,
  `Program.instantiationPoints`). The index in
  [citations.md](citations.md) keeps the list current.
- **Where the compilers disagree with the text**, the model is the
  tiebreaker and the disagreements are recorded, never settled by
  majority: the P3606 shortcut in two different widths (GCC and Clang 21
  onward), Clang 17 to 20 checking conversions before constraints, the
  placeholder type-constraint in the tie-break gate on GCC and Clang 17
  and 18, and both compilers treating an ambiguous partial specialization
  as a deduction failure where the text makes the call ill-formed. Each
  is in [findings.md](findings.md#compiler-disagreements).

What "not unsound" does not claim: the model is a fragment. Types are
first-order, there are no parameter packs, expressions are an oracle,
name lookup is an input, and template-argument conversions are not yet
transcribed. A result about the Standard is a result about this fragment
of it.

## The typeclass side, module by module

The encoding, as the model has it. An instance is a partial specialization
of a variable template `functor<T>` whose primary is `std::false_type`.
Each operation is an object with one `operator()`, a function template
whose trailing `const auto &TC` parameter defaults to
`functor<std::remove_cvref_t<T>>` and whose constraint is the call through
`TC`. Instance lookup is therefore the Standard side's `selectInstance`,
and `coherence` and `stability` need nothing further. Everything below is
about what happens at the call.

### Encoding

`Overload/Typeclass/Encoding.lean`: `fmapObject tc` is the operation
object as one `FunctionTemplate`. `memberAtomics` answers the encoding's
two atomic constraints, the call through the instance (`fmap_call`, true
exactly when the lookup selects an instance, since an instance has the
operation and the primary does not) and the by-value route's shape
constraint; `encodingEnv p` is `Env.ofProgram` with those answers.

- `fmapObject_deduce`: deducing the operation object for a call is a
  function of instance lookup at the container's type with cv and
  reference removed, and of nothing else in the program. The
  specialization it produces (`fmapSpec`) names the lookup, not the
  instance, so it does not move when instance positions shift.
- `fmapObject_outcome`: the three cases. An instance selected, deduction
  succeeds. No instance, a soft failure, so the call is merely not viable.
  An ambiguous lookup, a hard error. Soft failure and the normalized key
  are discharged by construction.
- `call_stability`: declaring an instance anywhere leaves a call's
  resolution unchanged unless the instance matches the key; then the
  operation object becomes viable through it, or lookup is ambiguous and
  the call is ill-formed. The hypothesis `hothers` asks that no other
  candidate's deduction consult the lookup. Non-template functions meet it
  outright, and the library meets it because a variable cannot be
  overloaded.

### Routes

`Overload/Typeclass/Routes.lean`: the other ways an instance reaches a
call. `pinTemplate` is the pinning pattern of the library's examples, a
user template with a reference parameter defaulted to the lookup and no
constraint: `pinned_deduce`, with the instance given explicitly the lookup
is never instantiated and the outcome is the same in every program;
`unpinned_deduce`, with it omitted a missing instance binds the primary
and the call is viable, so the error is in the body. `byValueObject` is
`traverse`'s policy parameter reduced to `fmap`: `byValue_omitted_outcome`
follows lookup and fails softly only because `std::false_type` has no
instance's shape; `byValue_passed` never instantiates the lookup, and the
instance enters the specialization by its type. `valueRoute`, `typeRoute`
and `argumentRoute` are the plan's alternative design, as overloads beside
the canonical object, so the emitted cases can show where they separate
and where the type route is exposed to an ambiguous canonical lookup.

### Arguments

`Overload/Typeclass/Arguments.lean`: leak 4 of instance inheritance as a
theorem, and what closes it. `valueRouteAt b` is the value route with
its instance parameter typed as the instance class `b`;
`value_route_slices` says a derived instance value and the base's own
deduce the same specialization there, so an algorithm pinned to the
derived instance runs the base's. `pin_keeps_identity` says pinning two
objects is two specializations, since the reference parameter denotes
the object; it is the explicit-step half of `superclass_identity`. The
library's parameters are references, which is what closes the leak.
`value_route_needs_structural`: a derivation base keeps the
implementation as a protected base, so neither it nor an instance type
derived from it is structural, and neither can be a template argument
for a placeholder parameter at all. The value route is closed to the
library's instance types either way.

### Inheritance

`Overload/Typeclass/Inheritance.lean`: the instance-inheritance question
outside the fragment where `inheritance_erasure` holds.
`rank_beats_refinement`: a function naming an Applicative instance type
wins at that type and loses to a generic template at a Monad instance type
derived from it, because an exact match beats a derived-to-base
conversion before the non-template preference is consulted.
`erasure_needs_exact_type`: a function naming a base instance type
accepts the derived one and nothing after erasure.
`derived_class_deduction`: a parameter `const derive_functor<I>&` deduces
`I` from a Monad instance type derived from `derive_functor<opt_impl>`,
and stops once derivation becomes composition. `superclass_identity`: a
Functor retrieved from a stronger instance is a different template
argument from the canonical one, so the two can agree only in behaviour.
The practical rule falls out: inherit if you like, but never name an
instance type in a signature.

### Units

`Overload/Typeclass/Units.lean`: `operation_object_not_separated`. Two
units whose lookups select different instances deduce one specialization
of the operation object, because its instance argument is a reference to
the lookup variable, one entity in every unit, so the program gives one
function two meanings ([basic.def.odr]/16). `byValue_separated`: the
by-value route separates as far as instance types are distinct.
`call_stability_unit`: stability per unit; an instance after the call
leaves it unchanged, one before it moves it as `call_stability` says.

### Members

`Overload/Typeclass/Members.lean`: the member call `TC.fmap(...)` as a
parameter. The model does not resolve it; it is the atomic constraint the
environment answers. `fmapObject_member`: whatever the member call
answers, deducing the operation object is that answer once the lookup is
instantiated. `member_transfer` spells out the three outcomes;
`ofProgram_member` says `encodingEnv` is the accurate member;
`inaccurate_member_ill_formed` shows a member that is hard to check, as
an unconstrained member with a deduced return type is, makes the call
ill-formed though the lookup selected an instance and it is the only
candidate. The object adds nothing and loses nothing, so accuracy is owed
by whoever writes the member.

`withExtraObject` is a second `operator()` of different arity, as
`fold_map` and `combine_all` have. `arity_disjoint_soft` and
`call_stability_arity`: neither reaches the lookup in a call of the
other's arity, provided the lookup default is placed after a parameter the
shorter call cannot deduce; `arity_order_matters` shows the default placed
first substitutes an ambiguous lookup in a call meant for another
`operator()`. `algorithm_transfer`, `algorithm_accurate` and
`call_order_matters` read the Standard side's `Conjunction` for an
algorithm whose constraint is the member calls its body makes.

### Lookup

`Overload/Typeclass/Lookup.lean`: what lookup finds for the operation
object as beman.transpose declares it, `struct fmap_fn { operator()...
}; inline constexpr fmap_fn fmap{};` (`opClass`, with the `operator()`
being `fmapObject` under that name in the class's scope,
`operatorMember`). `object_design_candidates` and `opClass_candidates`:
a call `fmap(f, x)` whose unqualified lookup binds `fmap` to the object
resolves over the class's call operators and nothing else, whatever the
argument types' namespaces declare. `call_stability_object`:
resolution over the object's one `operator()` moves exactly as
`call_stability` says, with `hothers` discharged, since there is no
other candidate to consult the lookup. This is the "no other lookup on
the name" row of [obligations.md](obligations.md), now a theorem of the
lookup rules rather than a hypothesis.
`unconstrained_member_hides_constrained`: the member call through an
instance type whose own `fmap` is unconstrained never reaches the
derivation base's constrained one, which is the audit's finding against
the library's Functor instances as a theorem.

### Emit

`Overload/Typeclass/Emit.lean`: the encoding's emitted cases, with a
prelude in which `selected<K>` has `fmap`, so a partial specialization's
value is an instance, and the concepts `fmap_shape` and `fmap_call` are
declared. Their expectations are computed in `encodingEnv`.

## From theorems to obligations

An obligation is a hypothesis a theorem needs that the language does not
guarantee. The harvest is mechanical: read each theorem's hypotheses and
ask who has to make each one true. The table in
[obligations.md](obligations.md) is the result; this is how a few rows
came to be.

- `call_stability` takes `hsoft` and `hhard`, that the lookup's primary is
  the soft design. That is the soft-primary row, owed by the typeclass
  author and met by `std::false_type`.
- `call_stability` takes `hothers`, that no other candidate consults the
  lookup. That is the no-other-lookup row. The library meets it because
  each operation is a variable, which cannot be overloaded.
  `call_stability_arity` refines it for operation objects with two
  `operator()`s, and `arity_order_matters` says what the placement owes.
- `inheritance_erasure` takes `ExactPair` and `NoDerivedDeduction`. That
  is the exact-type-use row, and the three theorems in
  `Typeclass/Inheritance` are what happens when it is not met.
- `fmapObject_member` takes the member call's answer as a parameter. That
  is the accurate-members row, and the audit of beman.transpose found it
  unmet in every typeclass.
- `verdicts_single` and `late_insertion_verdict` tie the visibility row to
  [temp.point]/7 and [temp.spec.partial.general]/1, and
  `registry_verdicts` ties the Monoid registry to [temp.constr.atomic]/3.
  These rows are undiagnosable, and now they say which rule the program
  breaks.
- `byValue_separated` takes distinct instance types; that row is owed by
  instance authors and the library passes stateful monoids by value, so
  it is live there.

The probes of the library itself (`probes/library/`, recorded in
[probes.md](probes.md#library-probes)) checked the two obligations the
model takes as given, accurate members and visible instances, against
beman.transpose, and the algorithm probes checked what an algorithm handed
an instance can rely on. What they found, and where it stands:

| Found | Issue | State |
|---|---|---|
| `derive_applicative::invoke` unconstrained, so soft failure depends on each instance re-exposing a constrained member | #6 | Fixed (PR #9) |
| An `ap`-only Applicative basis accepts a function it cannot call and returns an unsaturated partial | #7 | Fixed (PR #9) |
| Monad and Traversable derived members hard-error on probes | #8 | Fixed (PRs #15, #16) |
| Functor instances for `optional` and `vector`: an unconstrained `fmap` hides the constrained derived one | #10 | Fixed (PR #22) |
| `std::array` Applicative `invoke` constrained on shape only | #11 | Fixed (PR #22) |
| Derived members whose constraints are weaker than their bodies | #12 | Fixed (PR #21) |
| `optional` Monad `bind` accepts a non-monadic continuation | #13 | Fixed (PR #23) |
| Instances for std types declared outside the typeclass header: late inclusion is ill-formed with no diagnostic required | #14 | Open, PR #27 |
| `zip_list` and the sender copy the callable without saying so | #17 | Open, PR #24 |
| `void`-returning callables are a hard error on a probe | #18 | Open, PR #24 |
| The accumulating applicative's refused `bind` is a `static_assert`, so asking `monad_object` of it is a hard error | #19 | Open, PR #25 |
| `lifted_monoid` and `kleisli_monoid` construct their own object, so a stateful one is never consulted | #20 | Open, PR #26 |

The issue numbers are steve-downey/typeclass. None of these changes the
value a computation returns. What they change is whether a wrong call is
refused cleanly, refused with a hard error, or accepted and wrong later.

## What carries beyond typeclasses

Anyone writing a customization point object, a tag-dispatched algorithm,
or a trait specialized across headers meets the same rules. The results
that transfer, stated without the typeclass vocabulary:

- A constraint that is the operation the body performs makes the object
  transparent: it is viable, not viable or ill-formed exactly as the
  underlying call is (`fmapObject_member`). The accuracy of that
  underlying call, and in particular whether a probe of it instantiates a
  deduced return type, is what decides whether a wrong call is a clean
  "no" or a hard error.
- A defaulted template parameter whose default instantiates something
  that can fail hard is instantiated for every candidate deduction
  reaches, and no requires-clause on that template can guard it
  (`constraint_cannot_guard_default`). Place such a default after a
  parameter a mismatched call cannot deduce (`arity_order_matters`).
- Priority-tag dispatch evaluates every overload's constraint
  (`dispatch_hard_condition`). A constraint-exclusion chain or `if
  constexpr` stops at the first that holds.
- `enable_if` in a trailing return type does not shield the parameters,
  and loses to a requires-clause in partial ordering (`sfinae_unshielded`,
  `sfinae_loses_subsumption`).
- A conjunction of requirements is checked in the order written, and a
  guard placed after what it guards protects nothing
  (`conjunction_answers`, `call_order_matters`).
- Adding a specialization of a variable or class template to a program
  changes selection only at arguments it matches, and there only to it or
  to ambiguity (`stability`). A specialization declared after a use, or
  visible in one translation unit and not another, is ill-formed with no
  diagnostic required by [temp.point]/7 or [temp.spec.partial.general]/1,
  and a registry tested by completeness has the same verdicts under
  [temp.constr.atomic]/3 (`late_insertion_verdict`, `registry_verdicts`).
  GCC 16 diagnoses the first; Clang 23 keeps the stale answer.
- Naming a concrete class in a signature beside a generic overload makes
  derived-to-base conversions compete with exact matches, and the exact
  match wins before any non-template preference or constraint is consulted
  (`rank_beats_refinement`, `separability_rank_precedence`).
- Resolution ignores access. A protected base is selected through and
  the call is ill-formed, not non-viable
  (`protected_base_selected_ill_formed`).
- An operation declared as an object, a customization point object for
  one, is the whole of what lookup finds for its name: no function of
  that name in an argument's namespace is ever a candidate
  (`object_suppresses_adl`, `object_design_candidates`), and no dependent
  call of it can get the verdict of [temp.dep.candidate]/1
  (`object_design_no_adl_verdict`). Declared as a function template, the
  same operation admits a user's overload beside the user's class, which
  wins (`free_function_admits_adl`), and a better overload in another
  unit is ill-formed with no diagnostic required
  (`late_adl_overload_verdict`).
- A member declared in a derived class hides every base member of its
  name, constrained or not (`derived_member_hides_base`). A probe through
  the derived class never consults the base's constraint
  (`unconstrained_member_hides_constrained`).

## Running things

| Command | What it does |
|---|---|
| `lake build` | Builds the model, runs `#check_citations`, `#check_layering` and every `#audit`. |
| `lake test` | Runs the `#guard` tests in `OverloadTest/`. |
| `make citations` | Regenerates [citations.md](citations.md) from the compiled environment. CI fails if it is stale. |
| `make drift-check` | Checks every cited section and paragraph exists in the pinned draft; `make drift-check-current` also reports paragraphs that differ on the draft's `main`. |
| `make differential` | Emits every case as C++ and compiles each with the compilers in `PROBE_COMPILERS`. A disagreement not listed in `differential/known-disagreements.txt` fails. |
| `make probes` | Reruns the hand-written probes in `probes/`. |
| `make probes-library BEMAN_TRANSPOSE_INCLUDE=dir` | Probes beman.transpose itself. |
