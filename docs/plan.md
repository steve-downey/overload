# Modelling C++ overload resolution in Lean: plan

Steve Downey, 13 October 2026. Transcribed into the repository on 15
October 2026; the decision log has moved to `decisions.md`, the probe
results to `probes.md`, and the standing findings to `findings.md`. Items
settled since are marked.

## Purpose

Build a Lean 4 model of the C++ selection mechanisms that the pure-library
typeclass technique depends on, and use it to show that the open
polymorphism it provides is sound and unsurprising.

The model covers template argument deduction, substitution failure
(SFINAE), Concepts constraints, Mandates, partial ordering, partial
specialization matching, and overload resolution. The typeclass encoding is
then defined on top of the model, and its properties are proved about that
definition.

Three deliverables:

1. **Stability theorems.** Instance lookup is coherent, and adding an
   instance cannot silently change the meaning of code that already
   resolved.
2. **Inheritance guidance.** A proved answer to whether instance types for
   related typeclasses (Functor and Applicative) may, should, or must not be
   related by inheritance.
3. **An obligations table.** The proof obligations a typeclass places on its
   authors and users beyond the algebraic laws, each classified by how it is
   discharged.

A fourth outcome is possible and would matter beyond this work: a place
where a supposedly well-understood part of the language behaves differently
once constant template parameters carry instances. The plan is arranged so
that such a result shows up as a specific failed proof.

Two further results are about the Standard itself. Some statements it
spells out will turn out to be theorems of its other rules, and identifying
them is useful. A statement that is inconsistent with the rest, or false,
would be a defect. That is not expected, but the model is built so it could
not pass unnoticed.

## Scope

The core is smaller than full overload resolution. Instance lookup runs
through variable-template partial specialization, which the standard
defines by rewriting to function-template partial ordering plus constraint
subsumption. Call-site overload resolution is a layer above that core.

In scope:

- Template argument deduction for type and constant template parameters,
  including default template arguments and non-deduced contexts.
- Substitution with three outcomes: success, deduction failure, and hard
  error.
- Constraints: normalization, atomic constraint identity, satisfaction,
  subsumption.
- Mandates, modelled as a check that runs only after selection.
- Partial ordering of function templates, and matching and ordering of
  partial specializations.
- Best viable function selection, with implicit conversion ranking supplied
  as a parameter.
- The typeclass encoding: canonical lookup, the three explicit-instance
  routes, and customization point objects that dispatch to an instance.

Out of scope at the start:

- Name lookup and argument-dependent lookup. The candidate set is an input.
- The general theory of implicit conversion sequences. One concrete ranking,
  for priority tags and reference binding, is supplied to assess
  user-written dispatch.
- The expression language. Expression validity is an oracle.
- Multiple translation units and points of instantiation.

Standing assumption: one translation unit, with every instance declared
before any use that would instantiate its lookup. This axiom hides the real
coherence hazards of C++, which are ill-formed with no diagnostic required.
It is stated explicitly so that a later phase can remove it
(`Overload.SingleTranslationUnit`, tagged `assumed "single-tu"`).

## Modelling approach

The model is a deep embedding of a small template language, with each
mechanism given twice: as a relation that transcribes the standard, and as
an executable function proved to agree with it.

- **Syntax as data.** Types, template heads, patterns, constraints and
  declarations are inductive types. A program is an ordered list of
  declarations, so declared-before-use is a checkable predicate.
- **Two outcome types.** Substitution and resolution each return more than
  success or failure, and the theorems are about the difference.
- **Expressions are an oracle.** An atomic constraint needs only to know
  whether its substituted expression is valid and whether it evaluates to
  true. The environment supplies that, so the expression language stays out
  of the model.
- **Conversion ranking is a parameter.** Phase 5 takes a structure giving
  which conversions exist and a preorder on them. The separability theorem
  quantifies over that structure.
- **Constant template arguments are structural values.** They are trees
  with decidable equality, and that equality is the model's
  template-argument equivalence.
- **Every definition cites the draft.** Each carries its stable name and
  paragraph as a checked attribute, such as `[temp.deduct.general]/5`, so
  the citation index can be generated and re-checked when the draft moves.
- **Executable means testable.** The executable side runs under `#eval` and
  drives a generator that emits C++ for the differential tests.

The two outcome types, as they stand in `Overload/Outcome.lean`:

```lean
inductive Subst (α : Type) where
  | ok   : α → Subst α           -- substitution succeeded
  | soft : Reason → Subst α      -- deduction failure, immediate context
  | hard : Reason → Subst α      -- ill-formed, diagnostic required

inductive Resolution (α : Type) where
  | selected  : α → Resolution α
  | noMatch   : Resolution α
  | ambiguous : List α → Resolution α
  | illFormed : Reason → Resolution α
```

`Subst` gains a fourth case for ill-formed with no diagnostic required when
the single translation unit axiom is relaxed.

## Traceability to the Standard

Every rule in the model names the sentence of the Standard it transcribes,
by stable name, and every statement is filed as a rule, a theorem, or an
assumption of ours.

Stable names such as `temp.deduct.general` survive renumbering between
drafts, and clause numbers do not. One paragraph often holds several rules:
paragraph 5 of `temp.deduct.general` holds the whole step order. So a
citation is a stable name, a paragraph and a sentence, per
citation-granularity.

The citation is an attribute, not a comment, so tools can check it:

```lean
@[std rule "temp.deduct.general#5.sentence-6"]
def checkConstraints ...

@[std theorem "temp.func.order#2.sentence-4"]
theorem constraints_only_break_ties ...

@[assumed "single-tu"]
def declaredBeforeUse ...
```

On a constructor the attribute is written as a command after the inductive,
`attribute [std rule "..."] Subst.ok`, since Lean does not accept attributes
in a constructor's declaration (`findings.md`).

Three checks follow from it:

- A lint fails the build when a constructor of a specification relation, or
  any axiom, carries neither a citation nor an assumption tag
  (`#check_citations` in `Overload.lean`).
- The citation index is generated from the environment (`make citations`,
  `citations.md`). It lists what rests on each sentence, and which in-scope
  sentences have no counterpart in the model.
- When the draft moves, each changed sentence maps to the definitions to
  re-examine (`make drift-check-current`).

| Class | Meaning | Form in Lean |
|---|---|---|
| Rule | A normative sentence taken as given. | A constructor of a specification relation, or a clause of a definition. |
| Theorem | A statement in the Standard that the model proves from the rules. | A theorem tagged with the sentence it restates. |
| Assumption | Something the model needs that the Standard does not say. | A tagged hypothesis or structure field, linked to its decision-log entry. |

Normative sentences start as rules. One is reclassified as a theorem when
it is proved from the others and then deleted from the rule set, which
confirms nothing else needed it. Notes and examples are not normative, so
they start as theorems: an example is a test with a stated outcome, and a
note that asserts a consequence is a proof target.

Rules are inductive relations and never Lean axioms. An inconsistent set of
axioms proves everything, so every theorem would pass silently. An
inductive relation cannot be inconsistent, so a conflict in the Standard
surfaces as a named theorem that fails. Each headline theorem is audited
with `#audit` (the `#print axioms` check) and may show only Lean's standard
axioms and tagged assumptions.

The four kinds of finding about the Standard are tabulated in
`findings.md`.

## Phases

Nine phases, each closed by a theorem or a passing test set. The typeclass
results first become reachable at phase 4, before any of call-site overload
resolution exists.

| Phase | Builds | Exit criterion | Needs |
|---|---|---|---|
| 0 Foundations | Repository, toolchain, citation attribute and its lint, test harness skeleton. Settles draft-pin, spec-style, library-dependency. | One definition cited end to end, and one emitted C++ program compiled locally by GCC and Clang. | |
| 1 Core syntax | Types, template heads with type and constant parameters and defaults, patterns, substitution, deduction, argument identity. | Deduction is sound and most general on the fragment, and the cost of its agreement proof is reported against spec-style. | 0 |
| 2 Substitution outcomes | The three-valued result, the immediate context, Mandates, and the step order of [temp.deduct.general]/5 as separate steps. | A hard error is absorbing, and the draft's own examples for that paragraph reproduce. | 1 |
| 3 Constraints | Normalization, atomic identity, satisfaction, subsumption. | Subsumption is a preorder and implies satisfaction-implication. | 2 |
| 4 Ordering and matching | Partial ordering of function templates. Partial specialization matching by the rewrite of [temp.spec.partial.order]/1. | Matching is deterministic. More-specialized is a strict partial order on the fragment, or the counterexample is recorded. | 3 |
| 5 Overload resolution | Viability and best viable function by [over.match.best.general]/2, over an abstract conversion ranking. | The separability theorem, with one lemma per suspect. Settles ranking-fidelity. | 4 |
| 6 Typeclass encoding | Canonical lookup, the three explicit-instance routes, superclass retrieval. | Coherence, stability, inheritance erasure, superclass coherence, and the obligations table. Settles missing-instance and instance-inheritance. | 4 for variable-template lookup, 5 for the call surface |
| 7 Differential testing | The C++ emitter and compiler runs. Starts in phase 1 and grows with each phase. | Every in-scope draft example and every counterexample agrees on GCC and Clang, or the disagreement is filed per test-oracle. | 0 |
| 8 Translation units | Points of instantiation, visibility, and the fourth substitution outcome. See single-tu. | Each obligation in the undiagnosable class is tied to a specific rule. | 6 |

Phase 6 can begin as soon as phase 4 closes. Phase 5 is on the critical
path only for the function-call surface and the by-value explicit-instance
route.

Status, 15 October 2026:

- Phase 0 is closed. The attribute, lint, index, drift check and emitter
  exist; `make differential` compiles eight emitted programs with GCC and
  Clang, all in agreement with the model.
- Phase 1 is open with its core in place: `Ty`, `Val`, substitution,
  deduction as relation and function with the agreement theorem
  (`deduceTy_iff`), determinism (`deduceTy_det`), the call-site adjustments
  of [temp.deduct.call]/2 to /5, template heads with defaults and
  explicit arguments (`deduceTemplate`), and template-argument equivalence
  (`Val.equivalent_iff`). Still to do: the most-general statement. The
  cost report is in `decisions.md#spec-style`.
- Phase 2 is open. The step order of [temp.deduct.general]/5 is
  transcribed as separate steps in `Overload/Steps.lean`, with the three
  outcomes, the immediate context (`form`), the oracle for separately
  instantiated constructs (`Env`), and the theorems: a hard error is
  absorbing (`defaults_hard_absorbing`, `deduceTemplate_hard_iff`), a
  requires-clause cannot guard a default
  (`constraint_cannot_guard_default`), and a constraint failure shields
  the function type (`constraint_soft_shields_function_type`). The
  paragraph's two examples and the example of /8 reproduce in Lean and as
  emitted C++. Still to do: Mandates as a post-selection check.
- Phase 5 is open as a skeleton, ahead of phase 3, because the P3606
  switch lives on it: `Overload/Resolution.lean` has candidate generation
  with the `Mode` switch, viability, and the best viable function by
  conversion sequences, the non-template preference and partial ordering,
  with the conversion ranking a parameter throughout. The emitted call
  cases are computed by `resolve` under the text with an identity-only
  ranking.
- Phase 4 is closed, with one proof target left open.
  `Overload/Ordering.lean` has the transformed template, deduction for
  partial ordering with the reference tie-breaks of
  [temp.deduct.partial]/9, more-specialized, the gate of
  [temp.func.order]/8 with template parameter equivalence from
  [temp.over.link]/6, and partial specialization matching by the rewrite
  of [temp.spec.partial.order]/1. Matching is deterministic
  (`patternMatches_iff`). More-specialized is irreflexive and asymmetric
  by theorem; transitivity was searched over 5832 triples of parameter
  shapes without a counterexample and is not yet proved. Subsumption
  ([temp.constr.order]/1 and /4) came with it so the gate has something to
  compare.
- Phase 3 is closed. Subsumption is propositional implication over
  atomic constraints read as free variables (`subsumes_iff`), hence a
  preorder (`subsumes_refl`, `subsumes_trans`,
  `atLeastAsConstrained_trans`). It implies satisfaction-implication up
  to hard errors (`subsumes_satisfied`), and the hard error happens
  (`subsumes_satisfied_hard`). The converse fails, with a witness
  (`satisfaction_implication_not_subsumes`). The example of
  [temp.constr.order]/1 is a theorem, and the note of /2 is refuted as
  worded (`findings.md`). Normalization of concept-ids is out of the
  fragment, which has none.
- Phase 6 is open with canonical lookup. `Overload/Typeclass.lean` has
  lookup over a program's instances (`Program.selectInstance`), with
  selection given as a relation as well (`Selects`, agreement theorem
  `select_iff`). Coherence and stability are proved and audited. Lookup
  selects an instance exactly when it is the most specialized match, and
  at most one is (`coherence`, `mostSpecialized_unique`). Otherwise it
  reports the primary or ambiguity, never an ill-formed program
  (`coherence_ambiguous`, `selectInstance_ne_illFormed`). Declaring an
  instance anywhere in a program moves lookup only at types the instance
  matches, and there only to it or to ambiguity (`stability`). Lookups of
  other typeclasses do not move (`stability_other_typeclass`). Neither
  theorem needs single-tu or soft failure (`findings.md`). Still to do:
  the explicit-instance routes, superclass retrieval, inheritance
  erasure, superclass coherence, termination, and the obligations table.

## Target theorems

Thirteen theorems carry the results. A theorem that fails is recorded with
its counterexample and is a finding, not a setback.

| Theorem | Statement | Phase |
|---|---|---|
| determinism | The same program and query always give the same outcome. | 4, 5 |
| mandate-inertness | Adding a Mandate to a candidate never changes which candidate is selected. It can only turn a selection into an ill-formed program. | 2, 5 |
| constraint-promotion | Turning a Mandate into a Constraint changes the outcome only by removing that candidate, so the result moves to the next best, to no match, or to ambiguity. | 5 |
| sfinae-requires | An `enable_if` encoding and a requires-clause with the same condition give the same viable set. They differ only where ordering consults subsumption. | 3, 5 |
| subsumption-sound | Subsumption is a preorder and implies satisfaction-implication, up to hard errors in checking the subsumed constraint. The converse fails, with a witness. | 3 |
| coherence | For a ground type, canonical lookup yields at most one instance or reports ambiguity. It never chooses silently. | 6 |
| stability | Adding an instance changes lookup only at types the new instance matches, and there only to the new instance or to ambiguity. | 6 |
| separability | The instance selected is invariant under the choice of conversion ranking. | 5 |
| inheritance-erasure | When every use takes instances at their deduced exact type, replacing derivation between instance types with composition plus retrieval changes no outcome. | 6 |
| superclass-coherence | The Functor derived from a stronger instance, such as `derive_functor<M>`, behaves as the canonical Functor instance where one exists. This is extensional equality of the operations, since the two are different types and so different template arguments. | 6 |
| termination | Lookup terminates under the restriction chosen in termination-condition. | 6 |
| divergence-separation | If two translation units resolve an instance differently, every function whose behaviour depends on that instance has a different identity in the two units. Expected to hold when the instance is a template argument of the function, and to fail when lookup happens inside a body. | 8 |
| dispatch-styles | For one ordered candidate list, the constraint-exclusion, if-constexpr and priority-tag encodings select the same candidate. Expected to differ only in whether having no candidate is a soft or a hard failure. | 5, 6 |

Stability is the theorem that says open polymorphism has no surprises. Its
hypotheses are expected to include soft failure of a missing instance and
the single translation unit axiom.

## Separability suspects

Conversion ranking is expected to factor out of instance selection. The
exposure is elsewhere: the order of deduction steps, and whether a failed
lookup is soft or hard. Each suspect below becomes one lemma under the
separability theorem.

| Suspect | What the draft says | Exposure |
|---|---|---|
| step-order | Default template arguments are substituted first. Constraints are checked next, then convertibility of non-dependent parameters, then the function type is substituted ([temp.deduct.general]/5). Instantiations triggered by substitution are outside the immediate context ([temp.deduct.general]/8). | A lookup in a defaulted constant parameter runs for every candidate deduction reaches, including ones that would lose. A requires-clause on the same template cannot guard it. If the lookup fails hard, the call is ill-formed. |
| argument-identity | Two values are template-argument-equivalent only if they have the same type. Class values compare by direct subobjects ([temp.type]/2). | Instance identity is type plus structure. A base sliced from a derived instance names a different specialization from the derived instance. |
| tie-break-reach | Constraints are compared only when the template parameter lists and function parameter lists have equal length, corresponding template parameters are equivalent, and function parameter types match ([temp.func.order]/8). Equivalence of constant parameters ignores type-constraints on placeholder types ([temp.over.link]/6). | A bound written as a type-constraint on an `auto` constant parameter keeps the tie-break. An extra defaulted parameter on one overload, or constant parameters of different concrete instance types, switches it off and leaves the pair ambiguous. |
| argument-conversion | Conversions of template arguments decide viability and are never ranked. The draft's own example is ambiguous between `template<int>` and `template<signed char>` ([temp.deduct.general]/12). | A second, unranked conversion relation for the literal-argument route. Whether a derived instance converts to a base-typed constant parameter is unchecked. |
| rank-precedence | Derived-to-base has Conversion rank ([over.best.ics.general]/7). Conversion comparison comes before template specialization and constraints ([over.match.best.general]/2). | The by-value route is the only one where ranking is live. It is an exact match unless instance types are related by inheritance or conversion. |

The step-order suspect has support in the draft itself. An example in
[temp.constr.atomic]/3 shows a call made ill-formed by a hard error in a
candidate that a better match would have beaten.

The tie-break entry corrects an earlier guess: equivalent template heads
are not required, only equivalent template parameters, so type-constraints
on placeholders do not disable it.

## Instance inheritance

The hypothesis is that inheritance between instance types is
selection-inert exactly when every use site takes the instance at its
deduced exact type. This is the question tracked as instance-inheritance.

The typeclass technique itself needs no subtype relation between instance
types. Use is duck typed, and the weaker instance can be derived from the
stronger one: a Monad instance's `as_functor` returns `derive_functor<M>`,
a fresh type that supplies the Functor operations from the Monad ones. The
relation varies by kind and may vary within a kind. Nothing forbids an
implementer from using inheritance instead, so the guidance has to say
whether that is safe.

Once a signature names an instance type concretely, inheritance becomes a
second ordering beside concept refinement, and the two can disagree. Four
leaks are known:

1. **Ranking beats subsumption.** Derived-to-base is a ranked conversion,
   and conversion comparison is consulted before constraints. An overload
   that should win by refinement can lose on rank.
2. **Deduction from a derived class.** A function parameter of the form
   `functor_impl<F>` deduces from a class derived from it, and fails if more
   than one base matches ([temp.deduct.call]/4). A derived Applicative
   silently matches Functor-shaped signatures.
3. **Two paths to the superclass.** Slicing an Applicative to its base gives
   one Functor and lookup gives another. They agree only if the base is the
   canonical instance, and the explicit-instance routes do not force that.
4. **Constant-parameter conversion.** Whether a derived instance is accepted
   for a base-typed constant template parameter is unchecked, and is a
   candidate for compiler disagreement. Settled 15 October 2026: accepted
   and sliced under C++26 (`probes.md`), so the leak is live.

Two theorems settle it. Inheritance erasure is the positive result: inside
the exact-type fragment, inheritance is only an implementation convenience.
Superclass coherence is a law on instance authors in every case, because
`derive_functor<M>` is a different type from the canonical Functor
instance, so the two can only agree in behaviour, never in identity. Leak 3
is therefore live today: a data type with a canonical Functor instance and a
Monad instance has two Functors, and nothing in the language makes them
agree.

Outside the fragment the model should produce a concrete counterexample for
each of leaks 1 to 3. The expected guidance is a checkable rule: inherit if
you like, but never name an instance type in a signature.

## Proof obligations

The obligations are harvested, not enumerated: every hypothesis a theorem
needs that the language does not guarantee is an obligation on someone. The
list is then complete relative to the theorems, and each entry has a proof
showing why it is needed.

The algebraic laws of each typeclass are excluded. These are the
obligations of the mechanism.

Each obligation is classified by how it is discharged:

- **By construction.** The library's design makes violation impossible.
- **Compiler-checked.** Violation is a required diagnostic.
- **Library-checkable.** A concept or `static_assert` can catch it.
- **Undiagnosable.** Violation is ill-formed with no diagnostic required, so
  only convention or tooling stands behind it.

The rows below are the candidates expected to fall out. The last column is
a prediction for the model to confirm or correct.

| Obligation | Owed by | Needed for | Expected discharge |
|---|---|---|---|
| Canonicity: at most one canonical instance per type, with no overlapping specializations left unordered. | Instance author | coherence | Compiler-checked within a translation unit |
| Visibility: the instance is declared before any use that would instantiate its lookup, identically in every translation unit. | Instance author | stability | Undiagnosable |
| Superclass coherence: the Functor derived from a stronger instance behaves as the canonical Functor instance, where one exists. | Instance author | superclass-coherence | A law on instance authors, since derivation synthesizes a new type rather than looking one up |
| Structural identity: the instance type is usable as a constant template parameter, and its equivalence is the identity intended. | Instance author | coherence | Compiler-checked for usability, convention for intent |
| Decreasing requirements: an instance requires instances only at proper subterms of the type it serves, and a derived instance such as `derive_functor<M>` requires only M. | Instance author | termination | Library-checkable |
| Soft failure: a missing instance fails as a constraint, not as a hard error. | Typeclass author | stability | By construction |
| Exact-type use: signatures take instances at their deduced type and never name an instance type. | Typeclass author | inheritance-erasure | Library-checkable |
| Visible refinement: the superclass relation is written so subsumption can see it. | Typeclass author | sfinae-requires | Convention |
| Stable satisfaction: a constraint gives the same answer at every point in the program ([temp.constr.atomic]/3). | Everyone | stability | Undiagnosable |
| Instance in the type: a data structure whose invariants depend on a non-canonical instance carries that instance in its type. | User of explicit instances | coherence | By construction for the two template-parameter routes |
| Instance in the signature: a function or class whose behaviour depends on an instance names it among its template arguments, and never looks it up only inside its body. | Typeclass author and user | divergence-separation | Convention |
| Genuine instance: an object passed as an explicit instance is meant as one. Instances are constrained by shape, not by a nominal type, so an arbitrary object of the right shape is accepted. | User of explicit instances | coherence | Library-checkable for shape, convention for intent |
| Normalized lookup key: const, volatile and reference qualifiers are stripped from a deduced type before instance lookup, so every spelling of a type reaches one instance. | Typeclass author | coherence | By construction if the dispatch normalizes |
| Shapeless default: `std::false_type`, the default instance, satisfies no typeclass's shape concept. | Typeclass author | coherence, stability | Library-checkable, one `static_assert` per typeclass |

The undiagnosable rows are the residual trust base. They are what the
single translation unit axiom hides, and they bear on the comparison with
Concept Maps: explicit opt-in removes accidental syntactic matches but not
these.

## Draft citations and prior art

The draft paragraphs this plan leans on were read in the working draft at
eel.is on 13 October 2026. The model cites the pinned text
(`decisions.md#draft-pin`); the drift check reports any cited paragraph
that differs on main.

Read and consistent with the plan:

- [temp.deduct.general] paragraphs 5, 8 and 12: step order, immediate
  context, unranked template argument conversions.
- [temp.deduct.call] paragraphs 4 and 5: deduction from a derived class,
  and failure when more than one base matches.
- [temp.func.order] paragraph 8: when constraints are compared.
- [temp.over.link] paragraph 6: equivalence of template parameters and
  template heads.
- [temp.spec.partial.order] paragraph 1: the rewrite of partial
  specializations to function templates.
- [temp.constr.atomic] paragraphs 2 and 3: atomic identity, satisfaction,
  and differing satisfaction as ill-formed with no diagnostic required.
- [temp.type] paragraph 2: template-argument equivalence.
- [over.match.best]: the order of the better-function rules, and the rank
  of derived-to-base.

Not yet checked:

- Resolved 15 October 2026: a derived class value is a valid argument for a
  base-typed class constant parameter under [temp.arg.nontype]/3 as
  rewritten by P2308R1. See the probe verdicts.
- The rules that make an instance declared after its first use ill-formed
  with no diagnostic required.
- Whether the initializer of a variable template specialization is outside
  the immediate context on every route the library uses. (The reconstruction
  finding on probe B in `probes.md` is evidence that it is, on Clang.)
- How Mandates in library wording map onto core language rules, which the
  model currently treats as a post-selection check.

Prior art, from memory, with titles and venues to confirm in phase 0:

- Siek and Taha, *A Semantic Analysis of C++ Templates*, ECOOP 2006. A
  formal semantics of templates, mechanized in Isabelle.
- Gregor, Järvi, Siek, Stroustrup, Dos Reis and Lumsdaine, *Concepts:
  Linguistic Support for Generic Programming in C++*, OOPSLA 2006. The
  design that included concept maps.
- Wadler and Blott, *How to Make Ad-hoc Polymorphism Less Ad Hoc*, POPL
  1989.
- Peyton Jones, Jones and Meijer, *Type Classes: An Exploration of the
  Design Space*, 1997.
- Dreyer, Harper and Chakravarty, *Modular Type Classes*, POPL 2007.
  Relevant to explicit instances and coherence.
- Selsam, Ullrich and de Moura, *Tabled Typeclass Resolution*, 2020. Lean
  4's resolution procedure.

No search has been made for mechanizations of C++ overload resolution newer
than these.

## First steps

- [x] Write the step-order probe: a defaulted constant template parameter
  whose lookup fails hard on a candidate that would lose. Run it on GCC and
  Clang locally, and on MSVC and EDG through Compiler Explorer.
- [x] Write the tie-break probe: two overloads that differ only by an extra
  defaulted template parameter, with one more constrained.
- [x] Check the four unchecked draft claims, and re-read the checked ones
  in the final C++26 text.
- [x] Settle draft-pin, spec-style and library-dependency.
- [x] Create the repository, pin the Lean toolchain, and add the citation
  attribute with its lint.
- [x] Define types, template heads and substitution, each with its
  citation.
- [x] Transcribe the step order of [temp.deduct.general]/5 as separate
  steps and reproduce that paragraph's examples.
- [ ] Confirm the prior art list and search for newer mechanizations.
