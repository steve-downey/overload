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
- **Citations are attributes.** `@[std rule "temp.deduct.general#5.sentence-6"]`,
  or several in one role, `@[std rule "a" "b"]`,
  on a definition says what sentence it transcribes. A second `std`
  attribute on the same declaration is an error, since a parametric
  attribute would otherwise replace the first in silence. `@[std theorem ...]`
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
three lints, `#check_citations`, `#audit`, `#check_layering`, and
`#rests_on decl`, which lists the sentences of the Standard a declaration
rests on, every citation in its transitive dependency closure with its
role, the assumptions among them, and the fields of the environment it
consults. It is how to tell a trait that is a theorem of the core rules
(`is_convertible` reaches [over.best.ics.general] and
[over.match.general]) from one that is primitive (`is_scalar` reaches
nothing past [basic.types]) or one that rests on an oracle (a
requires-expression's calls consult `Env.atomic`). `Overload.lean` runs
it on the judgements of phase 12; `restsOnKeys` is the same list as a
value, for tests. `#owes decl` is its companion for semantic requirements:
the `Semantic` constants in a declaration's closure, the laws a theorem
assumes, with `owes` the same list as a value; `coherence` and
`stability` owe none.

### Syntax

`Overload/Syntax.lean`: `Ty`, `Val` for constant template argument
values, substitution of bindings into a type (`Ty.subst`), and
template-argument equivalence. `Ty.fn params ret noexcept` is a
function type, with the parameter list a `nil`/`cons` chain like a
template argument list (`decisions.md#function-types`) and its exception
specification part of the type ([except.spec]/3); deduction compares it
as it compares a specialization, part by part, and the two
specifications must agree. `Val.Equivalent` transcribes [temp.type]/2
and `Val.equivalent_iff` says it is structural equality on the values the
fragment has. Constant arguments are structural values, trees with
decidable equality, and that equality is the model's notion of two
template arguments being the same.

### Types

`Overload/Types.lean`: the type categories of [basic.types] on the
fragment, and the structural type traits as queries. `integerTypes` is
the fragment's integer types with their ranges under LP64
(`decisions.md#integer-widths`) and `representable` whether a type
holds a value. `Ty.concrete` is a ground type the fragment can spell.
The primary categories, `isVoid`, `isIntegral`, `isPointer`,
`isLvalueReference`, `isRvalueReference`, `isClass`, `isFunction`, each
look through a top-level `const`; `Ty.primaryCategory` names the one
that holds, and `primary_category_unique` proves that exactly one does
of every concrete type ([meta.unary.cat]/3). The composite categories
follow [basic.types.general]/6 and /7: `isObject`, `isScalar`,
`isReference`, `isCompound`, `isFundamental`; `isConst` is top-level
only. `removeConst`, `removeReference`, `stripCvref` and
`addLvalueReference` are the transformations. `Trait` is the queries a
constraint can state. The structural ones (`Trait.structural`) are
answered by `Trait.answer` from the types alone, `soft` for a dependent
type or a wrong arity and never `hard` (`Trait.answer_not_hard`); the
rest ask about a program's classes and are `Program.trait`'s
(`Traits`).

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

`Overload/Constraint.lean`: constraints as `atomic`, `trait`, `conj`,
`disj`; satisfaction ([temp.constr.atomic]/3) as left-to-right
evaluation that treats an invalid substitution as not satisfied; and
subsumption ([temp.constr.order]/1) by disjunctive and conjunctive
normal form with atomic identity ([temp.constr.atomic]/2). An `atomic`
constraint is an expression by name and a `trait` constraint a `Trait`
query; the oracle answers an `Atom`, either kind, on the substituted
mapping. `Oracle.ofExpr` lifts an oracle for expressions alone, answering
traits structurally, and the environment a program defines answers them
from the program. A `requires` constraint is a
requires-expression, an atomic constraint of its own
([temp.constr.normal]/1): its requirements (`Requirement`: a call by
callee and argument types, a call on an object of a class, or a type),
with the bindings substituted into their types, go to the oracle as one
`Atom`. A `conceptId` is what normalization expands; one left unexpanded
names no concept the program declares, and the environment answers it
with a hard error. A clause element, `Atomic`, is an `Atom` with its
mapping, and `Constraint.answer` reads one, substituting into the head
too (`Atom.subst`).

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
`Decl`: classes with public and protected bases, their non-static data
members as `member` declarations after the class (`Member`: name, type,
and whether it has a default member initializer; `Program.membersOf`
lists them in order), their user-declared special member functions as
`special` declarations (`SmfDecl`: kind, body with a definition, `=
default` or `= delete`, and whether the parameter is a reference to
`const`), class templates, a concept with a constraint for its body
(`conceptDef`: name, arity, body over `Ty.param i`; the string-bodied
`concept` stays for the emitted C++ the model reads as one atom),
functions, function templates (`FunctionTemplate`: head, parameter types,
default arguments, return type, associated constraint, Mandates), a
variable template as `lookup` or `lookupHard` (a primary with a value, or
one whose instantiation fails), its partial specializations as `instance`,
a use of it, an object, a concept, and a user-defined conversion of a
class, `converting`: a converting constructor by its parameter type or
a conversion function by its target, each with its explicit flag and a
conversion function with the constness of its object parameter
(`UserConv`), declared after its class so the program stays a flat
list (`decisions.md#user-defined-conversions`). `Init` is the
initialization context, copy or direct: argument passing is copy, and
direct exists as the contrast that admits explicit candidates. Each
namespace-scope declaration
carries the scope it inhabits, a path of namespace and class steps from
the global scope inward, `[]` by default (`decisions.md#scope-syntax`).
`Program.candidates` is every declaration with a name, in order; `Scope`
reduces it to the overload set, one declaration per entity, and `Names`
computes what a call finds from a program point and a scope.
`SingleTranslationUnit` is the one tagged assumption of the development:
every partial specialization is declared before any use of its variable
template. `Units` removes it. `Program.normalize` is constraint
normalization ([temp.constr.normal]/1): a concept-id the program
declares is replaced by the concept's body with the arguments
substituted into the mappings of its atoms, fuel-bounded by the
program's length, and `Program.normalizeDecl` gives a function template
its associated constraints, the normal form of its constraint-expression
([temp.constr.normal]/2), which `Program.call` applies to its candidates
before resolution, so satisfaction and subsumption see atoms and a
refined concept subsumes the concept it refines.

### Arguments

`Overload/Arguments.lean`: the conversion of a constant template argument
to its parameter's type ([temp.arg.nontype]). The integer types and
their ranges are `Types`'s; here `literalType` is the type of an
integer literal ([lex.icon]/3), and
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
type; a class type, whose value is the argument's or, through the
environment's `initializer` oracle, the base subobject of a derived
value or the object a converting constructor makes; an lvalue
reference, which binds an object and refuses a temporary
([temp.arg.nontype]/6), as does a reference placeholder given a value
(`bindsTemporary`, `placeholder_reference_refuses_value`). The conversion never fails hard
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
`initializer`, the value of the candidate initializer `constexpr T v =
A;` for a class value supplied to a class-typed parameter, which
`Env.ofProgram` computes from the program's classes and conversions
(`Program.candidateInitializer`, in `Ranking`).
`deduction_ignores_conversion`: the call step never consults
convertibility, so which conversions exist, user-defined ones among
them, changes no deduced binding ([temp.deduct.call]/4).

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
`conversion_identifies`: two values of other classes that each
copy-initialize a class-typed parameter through a user-defined
conversion sequence are one specialization, since the candidate
initializer is the class's one value either way.
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

`Overload/Ranking.lean`: the one concrete ranking, `Program.ranking`.
`Program.standardIcs` forms the standard conversion sequence over class
hierarchies: the identity conversion, derived-to-base
([over.best.ics.general]/7, Conversion rank) and direct reference
binding ([over.ics.ref]/1); `better` compares two by the tiers of
[over.ics.rank]/3 as a lexicographic chain, `better_iff` is the
agreement with `BetterConv`, and `better_asymm`, a theorem of
[over.ics.rank]/1, says the ordering is asymmetric for any class
hierarchy.

On top of that, the user-defined conversion sequences of phase 11.
`Program.userConversions` lists the candidates of an initialization,
the constructors of the target and the conversion functions of the
source, an explicit one only for direct-initialization
([over.match.copy]/1, [over.match.ctor]/1, [over.match.conv]/1).
`Ics` is an implicit conversion sequence: standard, user-defined, with
the two standard sequences around the conversion and the class that
declares it ([over.ics.user]/1), or the ambiguous conversion sequence
([over.best.ics.general]/12). `Program.ics` forms it in an
initialization context: the standard sequence when one forms, which it
does for the argument's own class and its bases, else the best
user-defined sequence among the candidates, chosen by overload
resolution over the one argument with the second sequence as the
tie-break ([dcl.init.general]/15), a reference parameter binding the
converted temporary ([over.ics.ref]/2, /3); `IcsForms` and `ics_iff`
are relation and agreement, `ics_standard` says a standard sequence is
always the sequence, and `ics_one_user_defined` that one value goes
through one conversion ([class.conv.general]/4), which the type of
`Ics` makes so. `explicit_never_implicit`: no sequence in the copy
context goes through an explicit conversion. `betterIcs` ranks the
sequences, a standard one above every user-defined one
([over.ics.rank]/2, `standard_beats_user_defined`), two user-defined
ones through the same conversion by their second sequences, and the
ambiguous one indistinguishable from any; `BetterIcs`, `betterIcs_iff`
and `betterIcs_asymm` as before. `Program.ranking` is this, in the
copy-initialization context of argument passing, and the environment's
convertibility is the same `ics`, so deduction and ranking agree on
what converts. `Program.conversionFree` and `ics_free` say a program
without conversions forms only standard sequences.

`Program.candidateInitializer` is the oracle the environment carries for
a class value supplied to a class-typed constant parameter
([temp.arg.nontype]/3): the base subobject when the standard sequence
forms, the class's one value, `Program.uniqueValue`, when the
copy-initialization goes through a user-defined sequence, and none
when no sequence forms or the sequence is ambiguous. A class value in
the fragment lists its base subobjects and nothing else, so a class has
one value whichever constructor made it (`candidateInitializer_user`).

### Virtual

`Overload/Virtual.lean`: virtual functions, phase 14. `Virt` is a field of
`Decl.function` and of a destructor's `SmfDecl`: no specifier, `virtual`,
pure, `override` or `final` ([class.virtual]/1, /4, /5, [class.abstract]/2,
[class.dtor]/11). `Program.virtualFunctions c` is the virtual functions
a class's objects have, its final overriders: the class's own member
functions declared virtual or overriding, and the bases' that no member
overrides ([class.virtual]/1, /2). Overriding is `sameSignature`, the same
name and parameter-type-list, which is correspondence on two function
declarations (`override_is_correspondence` in `Overload/Scope.lean`, above
this module in the layering); a function of the same name with another
parameter list hides and does not override, the note of [class.virtual]/3,
which `hidden_virtual_example` reproduces. `polymorphic` is a virtual
function or a virtual destructor; `abstract` is a pure function among the
final overriders or a pure destructor ([class.abstract]/2, /4);
`virtualDtor` is a destructor declared virtual or a base's, since
prospective destructors correspond (`virtual_destructor_inherited`, a
rule N5054 states nowhere in one sentence). `abstract_polymorphic`: an
abstract class is polymorphic. `virtualsWellFormed` is the program-level
check that nothing overrides a `final` function, every `override`
overrides something, and no potentially-throwing member function
overrides a non-throwing virtual one ([except.spec]/5,
`override_keeps_noexcept` on the draft's example).

### Special

`Overload/Special.lean`: the special member functions. `Program.special c k`
is the special member of kind `k` that class `c` has, if any: the
user-declared one, a `special` declaration or a converting constructor of
copy or move form ([class.copy.ctor]/1, /2), or the implicitly declared
one, with its suppression and its parameter form ([class.default.ctor]/1,
[class.copy.ctor]/6 to /8, [class.copy.assign]/2, /4, [class.dtor]/2).
`Program.deleted` is "defined as deleted" for a defaulted one, the bullets
of [class.default.ctor]/2, [class.copy.ctor]/10, [class.copy.assign]/7 and
[class.dtor]/7, each about a member's type or about overload resolution
over a subobject's class to find its corresponding constructor or
assignment and whether that results in a usable candidate
([over.match.general]/4); `Program.trivial` and `Program.eligible`
likewise, with the no-virtual-functions conjunct of every triviality
rule read as `!polymorphic` (`polymorphic_not_trivial`).
`Program.throwing c k` is the exception specification of a special member
([except.spec]/4, /7 to /9): a user-declared member's specifier; for a
destructor or a defaulted member without one, the implicit rule,
potentially throwing exactly when a constructor, assignment or
destructor the implicit definition invokes on a potentially constructed
subobject is, found by the same resolution as deletion, or when a default
member initializer may throw (`Member.throwingInit`); a user-provided
member without a specifier is potentially throwing. `throwingWithin` is
shaped like `trivialWithin`, with the facts at the fuel below.
`implicit_noexcept_from_subobjects`: a flat class's special members are
all non-throwing. `nothrow_propagates`: a subobject's potentially-throwing
destructor makes the enclosing destructor potentially throwing, stated
within fuel. `initThrowing` is whether a parameter's initialization from
an argument may throw: a user-defined conversion that does, or the
constructor a by-value class parameter's copy-initialization selects. Every judgement is fuel-bounded through the program, as
`derives` is, and the candidate lists and the resolution over them
(`ctorCandidates`, `assignCandidates`, `resolveAmong`) are parametrized
by `Facts`, the special members and their deletion at the fuel below, so
nothing is mutually recursive. `copyInitUsable` is the check `Program.call`
makes on a by-value class parameter: the constructor that copy-initializes
it from an argument of its class is not deleted. The value and reference
nature of a class, data and codata, are `valueNature` and
`referenceMember`, definitions and not rules: `deleted_flat` says which
members delete which defaulted special members of a flat class, one
without bases, class-typed members, initializers or declared specials,
`value_nature_flat` that such a class has value nature exactly when no
member is a reference or `const`, and `pointer_member_keeps_value_nature`
that a pointer member deletes nothing.

### Traits

`Overload/Traits.lean`: `Program.trait q args`, the program's answer to
every `Trait`. `is_base_of` is `derives` or the same class, access
ignored ([meta.rel]/3). `is_convertible` is the return statement of
[meta.rel]/6: `void` to `void` and nothing else with `void`, no function
type, otherwise the implicit conversion sequence of `declval<From>()` to
`To`, not ambiguous, and for the argument's own class or a base the
constructor it selects usable (`is_convertible_eq_ics`).
`is_constructible` is the variable definition of [meta.unary.prop]/9:
resolution over a class's constructors for direct-initialization with
the usable-candidate check (`trait_is_resolution`), a reference binding
one argument, a scalar taking none or one of its own type, and no
object of an abstract class at all ([basic.def]/5,
`abstract_not_constructible`); `is_convertible` to an abstract class by
value is likewise false, since the test function is a definition
([dcl.fct.def.general]/2).
`is_assignable` is resolution over the assignment operators, a `const`
object having none. `is_destructible` and the `is_trivially_` forms
read the special members: the operation selected is a special member
and trivial. `is_trivially_copyable` and `is_standard_layout` are
[class.prop]/1 and /2 on the fragment, `triviallyCopyableClass` and
`standardLayoutClass`, with `zeroOffsetWithin` the types at offset zero;
`is_empty` is no members, no virtual functions and empty bases;
`is_polymorphic`, `is_abstract` and `has_virtual_destructor` read
`Overload/Virtual.lean`. The `is_nothrow_` family is the base trait and
the operations the definition invokes known not to throw
([except.spec]/6): the constructor or assignment resolution selects, by
`Program.throwing`, and each parameter's initialization, by
`initThrowing`; `is_nothrow_convertible` the conversion of
[meta.rel]/6; `is_nothrow_invocable` the function type's own
specification and its parameters' initializations; `is_nothrow_swappable`
`std::swap`'s specification, the move constructor and move assignment
non-throwing ([utility.swap]/4), with a program that declares a `swap`
of its own left to the oracle. `nothrow_destructible_eq`:
`is_nothrow_destructible` is `is_destructible` for a program whose
destructors carry no `noexcept(false)`. `is_invocable` of a function
type or a pointer to one checks each argument's conversion sequence.
The residue (`decisions.md#trait-residue`) answers `soft`: a conversion
between two different non-class types, which the fragment's sequences
do not form, and `is_invocable` of a class callee, whose call is
resolved above the environment.

### Requires

`Overload/Requires.lean`: requires-expressions, above the member call.
`Program.requirementHolds` decides one requirement with its types
substituted: a simple-requirement is the call `callee(declval<args>()...)`
at the end of the program in the global scope, found by `callCandidates`
and resolved by `Program.call`, a hard error in generation staying hard
and anything else viable or not; a member call likewise through
`memberSearch`; a type-requirement is `validType`, a template-id whose
arguments match its template's head and whose defaults form, by
`explicitStep` and `defaultsStep`, a declared or fundamental class name,
or any other concrete type. `Program.requirementsHold` checks a
requires-expression's requirements in lexical order and stops at the
first that decides, an invalid one making it `false`
([expr.prim.req.general]/5): `requires_soft_is_false`,
`requires_false_stops`, `requires_hard_stops`; and a requirement calling
a member holds exactly where the member call is viable and well-formed
(`member_requirement_iff_call`). `Env.full` is the
program's environment with requires-expressions answered; the base
environment, `Env.ofProgram`, decides the calls a requirement makes and
their candidates' constraints, so a requires-expression nested in those
is answered softly, one level down. The emitters compute their cases in
`Env.full`.

### Models

`Overload/Models.lean`: what satisfies and what models. `Semantic`
(`Program`) is a slug and a statement nothing decides; `Decl.semantic`
attaches one to a concept's specification, and `Program.laws` collects
the requirements modelling a concept needs through the concept-ids its
body is defined in terms of. `Laws` is the oracle, a `Prop` a theorem
states. `Program.models env laws c args` is satisfaction of the normal
form of `c<args>` and every law held ([res.on.requirements]/1);
`models_satisfies` is the one direction the text gives.
`Program.conceptUses` lists the concept-ids a call's validity depends on,
those of the selected candidate's constraint at the deduced arguments
([res.on.requirements]/3), and `Program.modelVerdicts` gives
`satisfiedNotModeled` for each the arguments satisfy with a law the case
has not claimed ([res.on.requirements]/2); `satisfied_not_modeled_verdict`
says a law is a verdict exactly when it is unclaimed, and
`satisfied_not_modeled_example` reproduces [concepts.equality]/8, a type
that satisfies a concept and fails its implicit expression variations.
The vocabulary of [concepts.equality], `equalityPreserving`, `onDomain`,
`stable`, `nonModifying` and `implicitVariations`, is named here.

### Concepts

`Overload/Concepts.lean`: the library's concepts as the fragment states
them, `libraryConcepts`, a program of `conceptDef`s over the traits of
phase 12 with a residue atom for each expression the fragment lacks, and
a `semantic` for each requirement a concept's specification gives beyond
its body, with the equality-preservation laws of [concepts.equality]/4 on
every library requires-expression that does not say otherwise.
`destructible` is `is_nothrow_destructible`, which since phase 14 is the
real rule, so a class with `~X() noexcept(false)` satisfies none of the
object concepts. `same_as_symmetric` ([concept.same]/1), `regular_refines`, the chain from
`regular` down to `move_constructible` by normalization
([concepts.object]/1), `regular_invocable_semantic_only`, one normal form
and one law of difference ([concept.regularinvocable]/3), and
`regular_laws`, the ten laws modelling `regular` needs, are decided in
the kernel. `constructible_from` and `invocable` are stated for one
argument type after the first, since a concept-id takes a fixed number
of arguments.

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

`Overload/Environment.lean`: `Env.ofProgram p atomics extra traits`, the
environment a program defines. A trait atom is answered by `traits`,
the program's own `Program.trait` by default; an unexpanded concept-id
is a hard error; a requires-expression is answered softly here, since
its calls need the program's lookup, which lives above the environment
(`Requires`). Instantiating `trait<a>` is lookup: a
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
(`NoDerivedDeduction`), and the program declares no user-defined
conversion (`Program.conversionFree`): one between unrelated classes
could reach a touched class through a constructor's parameter or a
conversion function's target. The hypothesis is about conversions
rather than signatures because a template parameter deduced from one
argument can meet another argument of a derived type.
`deduceTemplate_congr`, on the
way, says deduction depends on the environment only through
instantiation, atomic answers, bases and convertibility. The theorem
takes the trait oracle as a parameter, the same on both sides: a trait
the program answers, `is_base_of` among them, can see erasure, so the
result is for a fixed trait oracle, structural or otherwise.

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
them. A seventh verdict, `satisfiedNotModeled`, is phase 13's: a call
whose selected candidate's constraint names a concept the arguments
satisfy with a semantic requirement unclaimed ([res.on.requirements]/2;
`Models`). The model says nothing about a program with a verdict, which is the
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
([over.best.ics.general]/2) and ranks an ambiguous conversion sequence
as a user-defined one; then, on the selected function, a by-value
parameter of abstract class type makes the call ill-formed
([expr.call]/7, `abstract_by_value_ill_formed`); then an argument whose
conversion is ambiguous makes the call ill-formed
([over.best.ics.general]/12); then the access check on its conversions
([conv.ptr]/3, [dcl.init.ref]/4), after ambiguity resolution
([class.conv.general]/2); then the Mandates. `call_eq_invoke`: when the
conversions are unambiguous and accessible, the checks change nothing. `protected_base_selected_ill_formed` and
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
functions, every class declared up front so a conversion or a parameter
can name a class defined later, a class's user-defined conversions in
its body, a constructor defined with an empty body and a conversion
function defined when its target is complete, a class or class template
declared in a namespace is named by
its qualified name wherever a type mentions it, a call case carries the
scope it is written in, and the functions the call resolves over are
numbered by entity in the lookup's order; a declaration of the callee's
name lookup does not find gets a `hidden<j>` return type. A
`memberCall` query is `obj.f(args)` on an object of a class, and a
`dependentCall` query instantiates the dependent call declared at a
position, rendered as a template whose trailing return type names the
call, so the function selected is observable and a lookup failure is a
substitution failure. A `trait` query asks a type
trait of argument types and asserts the program's answer,
`Program.trait`, against the `std::` trait, so every trait judgement is
tested against the compilers' own; a trait in a requires-clause is rendered as the `std::`
variable template, a concept-id as `C<args>`, a requires-expression as a
`requires { ... }` body of `declval` calls and `typename`s, and a
`conceptDef` as a concept definition over `T0, ...`. A data member is rendered in its class's body, with
`{}` when it has a default member initializer, and a declared special
member as `= default`, `= delete` or an empty body; a class with a
converting constructor that needs a default constructor declares one. A `Case` is a program, a
query (deduction, call, lookup, trait, or raw C++) and the expected
outcome. `render`
writes a translation unit whose `static_assert`s check the outcome in
unevaluated contexts; a case carries its own `prelude` of fixtures beyond
the common ones. `cases` are the Standard side's, and `computed`,
`computedCall`, `computedLookup`, `computedTrait` are what the model says, which the tests
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

Beneath all of that, phase 12 gave the model the type system the
encoding stands on. The type categories of [basic.types] are predicates
on `Ty`, with exactly one primary category holding of every concrete
type (`primary_category_unique`). A class has data members and
user-declared special members, and `Program.special`, `deleted`,
`trivial` and `eligible` decide which special member functions it has
and what they are, the deletion rules recursing through subobjects by
overload resolution over their classes; `Program.call` refuses a
by-value class parameter whose copy-initialization selects a deleted
constructor. Every type trait the fragment can state is `Program.trait`,
a judgement from those rules, with `is_constructible` and
`is_convertible` overload resolution with the usable-candidate check
(`trait_is_resolution`, `is_convertible_eq_ics`), and a trait in a
constraint is answered by the program's environment. A concept-id is
normalized into the associated constraints before satisfaction and
subsumption see it, and a requires-expression is an atom whose calls and
types the full environment decides in lexical order
(`requires_soft_is_false`, `requires_false_stops`, `requires_hard_stops`,
`member_requirement_iff_call`). The value nature of a class, data and
codata, is a definition and a theorem of the deletion rules
(`deleted_flat`, `value_nature_flat`, `pointer_member_keeps_value_nature`),
not a rule.

Phase 13 added the half of a concept that is not a constraint. A semantic
requirement is a named, cited statement nothing decides; modelling a
concept is satisfying it and meeting every requirement of its
specification and of the concepts it is defined in terms of
(`models_satisfies`); a call whose validity depends on a modelling the
arguments lack is ill-formed, no diagnostic required, and the verdict
names the law (`satisfied_not_modeled_verdict`). The library's concepts
are transcribed with their laws, and `regular` subsumes `semiregular`
subsumes `copyable` subsumes `copy_constructible` by normalization alone
(`regular_refines`), while `regular_invocable` differs from `invocable`
in a law and nothing else (`regular_invocable_semantic_only`). `#owes`
lists the laws a theorem rests on, and the headline theorems of lookup
rest on none.

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

### Conversion

`Overload/Typeclass/Conversion.lean`: leak 5 of instance inheritance,
the one the encoding avoids by design. A Monad instance type with a
conversion function to an Applicative instance type, unrelated by
derivation. `conversion_invisible_to_deduction`: a generic algorithm
deduces the Monad instance type and resolves as it would without the
conversion, since deduction never applies one. `conversion_loses_rank`:
beside an overload naming the Applicative instance type the generic
template wins at the Monad instance type, by rank, before the
non-template preference. `converting_sites_ambiguous`: two overloads
reached by two conversions are ambiguous. `converted_instance_temporary`:
pinning a converted instance, a prvalue, is a deduction failure of the
pinning template, whose reference parameter would bind a temporary; and
`value_route_identifies_converted`: under the typed value route every
instance value that converts to the parameter's class names one
specialization. `explicit_conversion_dead`: an explicit conversion is
formed by no call. Refinement by a concept on the shape and a retrieval
function has none of these costs (`obligations.md`).

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

### ValueNature

`Overload/Typeclass/ValueNature.lean`: phase 12 on the encoding, on
concrete programs. `instance_shape_regular`: an instance type with no
data members and no declared special member, flat or derived from such,
has value nature and is trivially copyable, empty, standard-layout and
default, copy and move constructible, so the value route's copy of it
costs nothing. `reference_member_instance`: an instance type holding a
reference is structural, so the value route admits it, and is neither
default constructible nor assignable; structural and value nature are
different properties. `copy_constraint_shields`: the callable-copying
rule as a theorem, the trait `is_copy_constructible` as a constraint
making the algorithm not viable at a callable whose copy constructor is
deleted, where the same trait as a Mandate, the body's copy, makes the
call ill-formed. `refinement_normalizes` and `refinement_selects`: the
Monad concept's normal form subsumes the Functor concept's where the
two compared by name would not, and a call constrained by Functor and
one by Monad select the Monad overload at a Monad instance.
`member_probe_accurate`: a requires-expression probing a member says
what the member call says, the accurate-members obligation as the
Standard states it (`member_requirement_iff_call` on the Standard side).
Phase 14: `virtual_instance_costs`, an instance type with a virtual
operation keeps value nature and stays structural, so the value route
admits it, but is neither trivially copyable nor standard-layout nor
empty, so the route's copy of it is a real copy;
`abstract_instance_by_reference`, an abstract instance type is not
constructible and an algorithm taking it by value is ill-formed to call
even with a concrete derived instance, so only a reference reaches it;
`instance_nothrow`, an instance type with no data members has
non-throwing special members and satisfies `destructible` and the
`is_nothrow_` traits the value route relies on; `nothrow_copy_constraint`,
the noexcept-correct callable-copying rule, `is_nothrow_copy_constructible`
in the constraint making the algorithm not viable at a callable whose
copy may throw, where `is_copy_constructible` alone admits it.

### Laws

`Overload/Typeclass/Laws.lean`: the Functor, Applicative and Monad laws
and the superclass agreement as `Semantic`s on the encoding's concepts,
with their source in each statement and no citation, since the Standard
does not state them. `monad_laws` lists the eight modelling Monad needs.
`superclass_coherence_owed` is the obligations table's undiagnosable row
as a theorem: the Monad-constrained algorithm selects at an instance
whose shape satisfies the concept, the verdict names the superclass
agreement when every other law is claimed and it is not, and there is
none when it is claimed too. `shape_without_laws` gives an instance with
the shape and no law every law as a verdict. That `coherence`,
`stability`, `call_stability`, `inheritance_erasure` and
`superclass_identity` owe no law is an audit, `#owes`, and a test.

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
