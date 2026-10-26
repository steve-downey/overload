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
- Since phase 12: the type categories of [basic.types], data members and
  function types; the special member functions, implicitly declared,
  defaulted, deleted and trivial; the type traits the fragment can state,
  as judgements of the program; requires-expressions of calls and types;
  and concept-ids, normalized into the associated constraints.
- Since phase 15: class templates with bases and members, a
  specialization's members by substitution when it is looked into, and
  member templates of class templates.

Out of scope at the start:

- Name lookup and argument-dependent lookup. The candidate set is an input.
- The general theory of implicit conversion sequences. One concrete ranking,
  for priority tags and reference binding, is supplied to assess
  user-written dispatch. Phase 11 brings the user-defined conversion
  sequence in.
- The expression language. Expression validity is an oracle. Phase 12
  takes the type traits and requires-expressions the fragment can state
  out of the oracle, as judgements over the types, the special member
  functions and the calls the model already decides; the oracle keeps
  the residue.
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
in a constructor's declaration (`findings.md`). A declaration that
transcribes several sentences cites them in one attribute, `@[std rule
"a" "b"]`: a parametric attribute keeps one parameter per declaration, so
a second `std` attribute is refused with an error (`findings.md`).

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

Fifteen phases, each closed by a theorem or a passing test set. The
typeclass results first become reachable at phase 4, before any of
call-site overload resolution exists. Phase 9 was added on 20 October
2026, after the others closed, phase 10 on 21 October 2026, phase 11 on
23 October 2026, phases 12 to 14 on 24 October 2026, and phase 15 on 25 October
2026.

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
| 9 Declarations and lookup | Scopes, correspondence, unqualified and argument-dependent lookup, member lookup, the dependent-call verdict, entity identity across units, as P1787R6 rewrote them. See [below](#phase-9-declarations-and-where-to-find-them). | The candidate set of a call is computed, not given; every lookup claim the obligations rest on is a cited theorem. Settles lookup-scope and scope-syntax. | 5, 8 |
| 10 Template arguments | The conversion of a constant template argument to its parameter's type: converted constant expressions and narrowing, class values sliced to a base, placeholders, and the identity of specializations through the converted values. See [below](#phase-10-template-arguments-and-their-conversion). | Every explicit and default constant argument is converted by a cited rule, the example of [temp.deduct.general]/12 reproduces, and leak 4 of instance inheritance is a theorem. Settles integer-widths and value-typing. | 2, 6 |
| 11 User-defined conversions | Converting constructors and conversion functions, the user-defined conversion sequence and its rank, the ambiguous conversion sequence, reference binding to a converted temporary, `explicit` through the initialization context, and the conversion's effect on deduction and on constant template arguments. See [below](#phase-11-user-defined-conversions). | The concrete ranking forms every sequence of [over.best.ics.general]/3 the fragment can spell, with agreement and asymmetry; the four conversion theorems about the encoding are proved. Settles user-defined-conversions. | 5, 10 |
| 12 The type system, special members and traits | The type categories and data members, function types; the special member functions as implicitly declared, defaulted, deleted and trivial; the type traits and requires-expressions as judgements over those, with concept-ids normalized; the value and reference nature of a type as a theorem of the deletion rules. See [below](#phase-12-the-type-system-special-member-functions-and-traits). | Every trait the fragment can state is computed from cited rules and agrees with GCC and Clang on the emitted cases; the special members of a class are a cited judgement with agreement; the callable-copying rule and refinement subsumption are theorems of the encoding. Settles function-types, special-member-fragment, trait-residue and value-nature. | 3, 9, 11 |
| 13 Semantic requirements | What satisfies and what models ([res.on.requirements]): a semantic requirement as a named, cited statement nothing decides; modelling as satisfaction plus hypotheses; the ill-formed-no-diagnostic verdict for a satisfied concept not modeled; the library's concepts transcribed with their laws; the typeclass laws named; an audit of the laws each theorem owes. See [below](#phase-13-semantic-requirements-what-satisfies-and-what-models). | Every law a headline theorem of the encoding rests on is named and listed by `#owes`; the library's object concepts subsume one another by normalization; the superclass-coherence obligation is a theorem with its law as hypothesis. Settles semantic-requirements. | 8, 12 |
| 14 Virtual functions, exception specifications, aggregates | Three stages, one each: virtual and pure virtual functions, overriding by correspondence, polymorphic and abstract classes, and their effect on triviality and layout; exception specifications on every function, the implicit ones of the special members, and the `is_nothrow_` traits; aggregates, their elements as the model's class values, brace and parenthesized aggregate initialization, and `is_aggregate` and `is_implicit_lifetime`. See [below](#phase-14-virtual-functions-exception-specifications-and-aggregates). | `is_polymorphic`, `is_abstract`, `has_virtual_destructor`, every `is_nothrow_` trait, `is_aggregate` and `is_implicit_lifetime` are computed from cited rules and agree with GCC and Clang on the emitted cases; the class value is the aggregate's element list; the encoding's instance types are aggregates with non-throwing special members. Settles virtual-fragment, exception-specification-fragment and aggregate-fragment. | 12, 13 |
| 15 Class templates and their members | Class templates with bases and members declared for the current instantiation; a specialization's members by substitution when it is looked into, the implicit instantiation of declarations; member templates of class templates; member lookup, the call on an object, the special members and the traits over specializations; the member call with its implied object argument; the point of instantiation of a specialization; the encoding's derivation base as the class template it is, and the operation object's constraint as a resolved member call. See [below](#phase-15-class-templates-and-their-members). | The member search of a specialization is computed from the template's declarations by cited rules; `is_invocable` of a specialization callee is computed and the class-callee residue is closed; the traits of specializations agree with GCC and Clang on the emitted cases; the operation object's constraint is resolved, not assumed, and the accurate-members obligation is a theorem for the reduced encoding. Settles class-template-members. | 9, 12 |

Phase 6 can begin as soon as phase 4 closes. Phase 5 is on the critical
path only for the function-call surface and the by-value explicit-instance
route.

Status, 15 October 2026:

- Phase 0 is closed. The attribute, lint, index, drift check and emitter
  exist; `make differential` compiles eight emitted programs with GCC and
  Clang, all in agreement with the model.
- Phase 1 is closed. Its core: `Ty`, `Val`, substitution,
  deduction as relation and function with the agreement theorem
  (`deduceTy_iff`), determinism (`deduceTy_det`), the call-site adjustments
  of [temp.deduct.call]/2 to /5, template heads with defaults and
  explicit arguments (`deduceTemplate`), and template-argument equivalence
  (`Val.equivalent_iff`). The cost report is in `decisions.md#spec-style`.
  Deduction is sound and most general on the first-order fragment, in
  `Overload/Generality.lean`. Substituting the deduced bindings into `P`
  gives `A` (`deduceTy_subst`). Any bindings that extend the starting
  ones and make `P` equal a non-dependent `A` extend the deduced ones
  (`deduceTy_most_general`). The fragment leaves out references inside
  `P`, where collapsing gives two solutions, and constant arguments that
  mention a parameter below the top, which are non-deduced.
- Phase 2 is closed. The step order of [temp.deduct.general]/5 is
  transcribed as separate steps in `Overload/Steps.lean`, with the three
  outcomes, the immediate context (`form`), the oracle for separately
  instantiated constructs (`Env`), and the theorems: a hard error is
  absorbing (`defaults_hard_absorbing`, `deduceTemplate_hard_iff`), a
  requires-clause cannot guard a default
  (`constraint_cannot_guard_default`), and a constraint failure shields
  the function type (`constraint_soft_shields_function_type`). The
  paragraph's two examples and the example of /8 reproduce in Lean and as
  emitted C++. Mandates are a post-selection check in
  `Overload/Mandates.lean`: `invoke` is resolution, then the selected
  specialization's Mandates, and the emitted cases are computed with it.
  mandate-inertness is a theorem (`mandate_inertness`, `invoke_selected`).
  constraint-promotion holds where the Mandate fails, as removal of the
  candidate, and where ordering does not change (`constraint_promotion`).
  It fails otherwise (`promotion_reorders`), so the target is restated in
  the table.
- Phase 5 is closed on its exit criterion. `Overload/Resolution.lean`
  has candidate generation with the `Mode` switch, viability, and the
  best viable function by conversion sequences, the non-template
  preference and partial ordering, with the conversion ranking a
  parameter throughout. `Overload/Ranking.lean` supplies the one
  concrete ranking that ranking-fidelity calls for, `Program.ranking`:
  the identity and derived-to-base conversions, direct reference binding,
  and the tiers of [over.ics.rank]/3 as a lexicographic chain, given as
  relation and function (`better_iff`) and asymmetric for any class
  hierarchy (`better_asymm`). The emitted call cases are computed with
  it, and convertibility during deduction uses the same relation.
  `Overload/Separability.lean` proves separability for any two rankings
  of any conversion types: if both select the candidate at one position,
  they select the same candidate, specialization and instance included
  (`separability`). One lemma per suspect: step-order, argument-identity,
  argument-conversion, tie-break-reach and rank-precedence. The ranking
  is still live, since it decides which candidate wins (`ranking_live`),
  and leak 1 of instance inheritance is a theorem
  (`rank_beats_refinement`). Eleven emitted cases cover ranking, priority
  tags and the leak, and every compiler agrees. sfinae-requires is in
  `Overload/Sfinae.lean` for `enable_if` in a trailing return type: the
  same viable set (`sfinae_requires`), the same resolution where ordering
  does not change (`sfinae_requires_resolve`), and the two places they
  differ, subsumption (`sfinae_loses_subsumption`) and step order
  (`sfinae_unshielded`). dispatch-styles is in `Overload/Dispatch.lean`,
  checked over the eight valuations of three conditions rather than
  proved for every length (`dispatch_styles`). Exclusion, priority tags
  and the if-constexpr chain select the first condition that holds. With
  none, the first two leave the call not viable and the chain is
  ill-formed. They also differ in which conditions are checked: priority
  tags check every overload's, so a later condition that fails hard
  makes the call ill-formed (`dispatch_hard_condition`).
- Phase 4 is closed.
  `Overload/Ordering.lean` has the transformed template, deduction for
  partial ordering with the reference tie-breaks of
  [temp.deduct.partial]/9, more-specialized, the gate of
  [temp.func.order]/8 with template parameter equivalence from
  [temp.over.link]/6, and partial specialization matching by the rewrite
  of [temp.spec.partial.order]/1. Matching is deterministic
  (`patternMatches_iff`). More-specialized is irreflexive and asymmetric
  by theorem. Transitivity is proved in `Overload/Transitivity.lean` for
  templates of type parameters whose parameter types have no reference
  (`moreSpecialized_trans`). It rests on the transitivity of the gate and
  of more-constrained, and on lifting a match against synthesized types to
  every substitution. With references the tie-breaks of
  [temp.deduct.partial]/9 enter, and there the evidence is still the
  search over 5832 triples of parameter shapes, which found no
  counterexample. Subsumption
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
- Phase 8 is closed. `Overload/Units.lean` makes a program a list of
  translation units, each resolved alone. The fourth outcome is a
  verdict about the program, ill-formed with no diagnostic required,
  naming the rule and the use and nothing more (`IllFormedNdr`): an
  instance declared after a use ([temp.point]/7), or one of another unit
  that a use would select ([temp.spec.partial.general]/1). For one unit,
  no verdict is exactly the old standing assumption (`verdicts_single`).
  divergence-separation fails for the canonical operation object, whose
  instance argument is a reference to the lookup variable
  (`operation_object_not_separated`), and holds for pinning and, as far as
  instance types are distinct, for the by-value policy
  (`byValue_separated`). Stability at the call surface is stated per unit
  (`call_stability_unit`): a call sees only the declarations before it.
  An instance declared after the call leaves it unchanged, and the program
  either stays free of a verdict at the call's use or gets the verdict of
  [temp.point]/7 (`late_insertion_verdict`). An instance declared before
  it moves the call as `call_stability` says, on the call's prefix. The
  single translation unit assumption is no longer built into any
  theorem's environment. The exit criterion holds: the undiagnosable
  obligations that make a program ill-formed are tied to [temp.point]/7,
  [temp.spec.partial.general]/1 and [basic.def.odr]/16. Exact-type use and
  superclass coherence are undiagnosable too, but their programs are
  well-formed, so there is no rule to tie them to (`obligations.md`).
- Phase 6 is open with canonical lookup. `Overload/Lookup.lean` has
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
  theorem needs single-tu or soft failure (`findings.md`). The operation
  object of beman.transpose is in the model, with its reference instance
  parameter (`Ty.ref`) and `remove_cvref_t` key, as four emitted call
  cases. An ambiguous instance there is a finding against both compilers
  (`findings.md`). The routes are settled by
  `decisions.md#explicit-instance-routes`. At the call surface,
  `fmapObject_outcome` proves that deducing the operation object follows
  lookup at the container's type with cv and reference removed. It
  succeeds when an instance is selected, fails softly when none is, and
  fails hard only when lookup is ambiguous. That discharges soft failure
  and the normalized lookup key by construction. The deduction is a
  function of that lookup alone (`fmapObject_deduce`), and its
  specialization names the lookup, not the instance, so it does not move
  when instance positions shift. Stability holds at the call surface over
  a whole candidate set (`call_stability`). Declaring an instance leaves a
  call's resolution unchanged unless the instance matches the key. When it
  matches, the operation object becomes viable through it, or the call is
  ill-formed by ambiguity. The other candidates must not consult the
  lookup, a hypothesis met by non-template functions outright. The
  library's other two routes are in the model, with `Ty.typeOf` for a
  policy type defaulted to the lookup's type. Pinning (`pinTemplate`) and
  the by-value policy (`byValueObject`) are emitted as nine cases. An
  explicit instance never instantiates the lookup (`pinned_deduce`,
  `byValue_passed`). Omitted, pinning has no constraint, so a missing
  instance is viable and fails in the body (`unpinned_deduce`). The
  by-value route fails softly only through the shapeless default
  (`byValue_omitted_outcome`). The plan's three routes are in the model
  as an alternative design (`valueRoute`, `typeRoute`, `argumentRoute`),
  in one overload set with the canonical object, with call cases that
  take explicit template arguments. The routes separate, but the type
  route does not protect a caller from an ambiguous canonical lookup, and
  the argument route cannot keep a default (`findings.md`). The
  obligations harvested so far are in `obligations.md`, with where each
  prediction held. Inheritance erasure is proved in
  `Overload/Erasure.lean` (`inheritance_erasure`). Erasing the base
  classes of a set of instance types changes no call that uses every
  class erasure touches at its exact type. Outside that fragment it does
  change outcomes (`erasure_needs_exact_type`). Superclass coherence
  cannot be a theorem of the model, which has no behaviour. What the model
  proves is that a retrieved Functor and the canonical one are different
  template arguments (`superclass_identity`), so agreement between them
  is a law on instance authors. Termination is vacuous for the library
  today, since no instance requires another. Deduction from a derived
  class ([temp.deduct.call]/4 and /5) is in the model, with bases that
  may be class template specializations, and leak 2 is a theorem
  (`derived_class_deduction`). Erasure therefore also asks that no
  argument of a touched class be deduced from as a derived class. The
  dispatch-styles check is under phase 5.
- The library audit, 18 October 2026, came after phase 8. Probing
  beman.transpose's own typeclasses (`probes/library/`, `probes.md`)
  found the member call through an instance, which the model took as
  accurate, inaccurate in every typeclass. `Overload/Typeclass/Members.lean` makes
  that answer a parameter. Whatever it is, the operation object passes it
  on unchanged (`fmapObject_member`, `member_transfer`), and the
  program's environment is the accurate case (`ofProgram_member`). Two
  further shapes the audit found are theorems too. An operation object
  with `operator()`s of different arity keeps stability when no other
  `operator()` reaches the lookup (`call_stability_arity`), and the
  placement of the lookup default decides whether it does
  (`arity_order_matters`). A registry tested by completeness, as
  `Monoid` is, has the verdicts of a lookup under a third rule
  (`registry_verdicts`).
- Phase 9 is closed, 20 October 2026, on its exit criterion: the
  candidate set of a call is computed from a program point and a scope,
  and every lookup claim the obligations rest on is a cited theorem.
  Planned the same day. The plan, the
  cross-reference against P1787R6 and the stages are
  [below](#phase-9-declarations-and-where-to-find-them). The in-scope
  paragraphs are in `Overload.Std.inScope`, so `citations.md` lists them
  as uncovered until each stage lands. Correspondence is done:
  `Overload/Scope.lean` has `corresponds` and `Corresponds` with their
  agreement, conflicts, and the overload set with one declaration per
  entity. redeclaration-inert is a theorem (`redeclaration_inert`), and
  the candidate list's ambiguity between a function and itself is a
  finding against the model (`findings.md`). Scoped lookup is done:
  declarations carry their scope, and `Overload/Names.lean` has single
  and unqualified search as relation and function, the classification of
  what lookup found, and a call from a point. inner-hides-outer is a
  theorem (`inner_hides_outer`), and five emitted cases agree with GCC
  and Clang. Argument-dependent lookup is done: `Overload/Adl.lean` has
  associated entities and namespaces, the lookup and when it applies,
  each as relation and function, and the call from a point now resolves
  over both lookups. object-suppresses-adl is a theorem on the Standard
  side (`object_suppresses_adl`, with `free_function_admits_adl` the
  contrast). Member lookup is done: `Overload/Members.lean` has the
  lookup set with its merge rule, the search in a class scope, the call
  on an object through its call operators, and a template under another
  name, so `Overload/Typeclass/Lookup.lean` can state the operation
  object as declared. object-suppresses-adl holds for the encoding
  (`object_design_candidates`), `call_stability` holds with `hothers`
  discharged (`call_stability_object`), and member-hiding is a theorem
  with the audit's hidden constrained member reproduced
  (`derived_member_hides_base`, `unconstrained_member_hides_constrained`).
  Nine more emitted cases agree with GCC and Clang. The dependent-call
  verdict is done: `Overload/DependentCandidate.lean` has the dependent
  call with its two contexts and the verdict of [temp.dep.candidate]/1
  beside phase 8's three. One unit has none
  (`dependentVerdicts_single`), the object design cannot get it
  (`object_design_no_adl_verdict`), the free-function design does
  (`late_adl_overload_verdict`), and the [temp.res.general]/1 example
  is a theorem and an emitted case. Three two-phase cases agree with
  GCC and Clang. Entity identity is done: every name of the fragment
  has external linkage (`Decl.linkage`), `sameEntity` carries the
  linkage condition of [basic.link]/8, and the one-definition rule's
  verdict at a lookup is `IllFormedNdr.odrMismatch`
  (`Units.odrVerdicts`), which `odr_verdict_implies_verdict` shows never
  comes first. The one paragraph of the phase left without a
  counterpart, [temp.point]/1, got one on 22 October 2026
  ([instantiation-points](#phase-9-declarations-and-where-to-find-them)):
  a declaration that refers to a specialization, `Decl.refersTo`, puts
  a point of instantiation after itself, the unit's end is another, and
  a call that means different things at two points is the sixth verdict
  (`laterCandidate`, `later_function_verdict`); a callee bound to an
  object has one meaning at every point (`object_design_one_meaning`).
  The emitted cases of the phase number twenty-three and every one
  agrees with GCC 15 and Clang 24; `make drift-check-current` reports one cited paragraph
  that differs on the draft's main, an editorial change
  (`decisions.md#draft-pin`).
- Phase 10 is closed, 21 October 2026, on its exit criterion: every
  explicit and default constant argument is converted by a cited rule
  (`convertArg`, in `Overload/Arguments.lean`, wired into the explicit
  and defaults steps), the example of [temp.deduct.general]/12 is a
  theorem (`temp_deduct_general_12_example`) and two emitted cases, and
  leak 4 of instance inheritance is a theorem (`slicing_identifies`,
  `value_route_slices`), closed by the library's reference parameters
  (`reference_keeps_identity`, `pin_keeps_identity`). Planned the same
  day; the plan, the cross-reference against N5054 and the stages are
  [below](#phase-10-template-arguments-and-their-conversion).
  narrowing-is-representability is `narrowing_constant`,
  conversion-shields-call is `conversion_soft_shields_call`. Nine
  emitted cases agree with Clang 24; the two with a derived value for a
  base-typed class parameter are rejected by GCC under the rule before
  P2308R1, the probe's finding reproduced (`findings.md`). One
  consequence beyond the plan: the library's derivation bases keep a
  protected base, so their instance types are not structural and the
  value route cannot take them at all (`value_route_needs_structural`).
  Every in-scope paragraph has a counterpart, since 22 October 2026.
- Phase 11 is closed, 23 October 2026, on its exit criterion: the
  concrete ranking forms every sequence of [over.best.ics.general]/3 the
  fragment can spell, standard, user-defined and ambiguous
  (`Program.ics`, `ics_iff`, `betterIcs_iff`, `betterIcs_asymm`), and
  the four conversion theorems about the encoding are proved, as six
  (`Overload/Typeclass/Conversion.lean`). conversion-invisible-to-deduction
  is `deduction_ignores_conversion` and `conversion_invisible_to_deduction`,
  conversion-loses-rank is `standard_beats_user_defined`,
  `conversion_loses_rank` and `converting_sites_ambiguous`,
  converted-argument-temporary is `placeholder_reference_refuses_value`,
  `converted_instance_temporary`, `conversion_identifies` and
  `value_route_identifies_converted`, and explicit-never-implicit is
  `explicit_never_implicit` and `explicit_conversion_dead`. Planned the
  same day; the plan, the cross-reference against N5054 and the stages
  are [below](#phase-11-user-defined-conversions), with two departures
  recorded there. Nineteen emitted cases, the draft's examples of
  [over.best.ics.general]/12 and [class.conv.general]/4 among them,
  agree with GCC 15 and Clang 24, with no new disagreement: GCC accepts
  a class-typed constant argument through a converting constructor
  while still rejecting a sliced one (`findings.md`). One correction to
  phase 10 on the way: a value for a placeholder reference parameter is
  refused, as [temp.arg.nontype]/6 says. Settles user-defined-conversions.
  Every in-scope paragraph has a counterpart, once the citation attribute
  learnt to keep several citations on one declaration (`findings.md`).
- Phase 12 is closed, 24 October 2026, planned and landed the same day,
  on its exit criterion with the departures its stages record: every
  trait the fragment can state is computed from cited rules and agrees
  with GCC 15 and Clang 24 on forty-seven emitted trait cases
  (`Program.trait`, `trait_is_resolution`, `is_convertible_eq_ics`); the
  special members of a class are a cited judgement (`Program.special`,
  `deleted`, `trivial`, `eligible`), fuel-bounded as `derives` is rather
  than a relation with agreement, observed through nine call cases; the
  callable-copying rule and refinement subsumption are theorems of the
  encoding (`copy_constraint_shields`, `refinement_normalizes`,
  `refinement_selects`); and the value nature of a class is a theorem of
  the deletion rules for flat classes (`value_nature_flat`). The type
  categories and data members, with function types; the special member
  functions by [special], [class.default.ctor], [class.copy.ctor],
  [class.copy.assign] and [class.dtor]; the traits and
  requires-expressions as judgements over those, with concept-ids
  normalized; the plan, the cross-reference against N5054 and the stages
  are [below](#phase-12-the-type-system-special-member-functions-and-traits).
  `is_invocable` of a class callee landed 25 October 2026, answered by
  the environment one level up as a requires-expression is
  (`full_invocable_class`; the stage 4 status below), with
  [func.require]/1 in scope. The general value-nature theorem landed 25
  October 2026 (`value_nature_iff`, `deletion_propagates`; the stage 3
  status below), and compound and nested requirements the same day
  (`compound_eq_simple_nested`; the stage 5 status below). Settles function-types, special-member-fragment,
  trait-residue and value-nature. Stage 2, type-categories, landed 24 October 2026:
  `Ty.fn`, `Overload/Types.lean` with the categories, the
  transformations, `primary_category_unique` and the structural
  `Trait` queries, `Constraint.trait` answered without the oracle,
  `Decl.member`, and eighteen emitted trait cases, all in agreement
  with GCC 15 and Clang 24. One departure: a data member is its own
  declaration after the class, `Decl.member`, as a conversion is,
  rather than a field of `Decl.class`, so the flat program and every
  match on `Decl.class` stand. Stage 3, special-members, landed the same
  day: `Overload/Special.lean` with `Program.special`, `deleted`,
  `trivial`, `eligible`, the candidate lists and resolution over them,
  `copyInitUsable` in `Program.call`, and nine emitted cases observing
  deletion through a by-value parameter, all in agreement with GCC 15
  and Clang 24. Three departures. A user-declared special member is its
  own declaration, `Decl.special`, like a member. The recursive
  judgements are fuel-bounded functions cited as rules, as `derives`
  is, not relations with agreement theorems; the fuel is the program's
  length, since a subobject's class is complete before the class that
  holds it. The value-nature theorems are stated for flat classes,
  `deleted_flat`, `value_nature_flat` and
  `pointer_member_keeps_value_nature`, where the deletion rules reduce
  to the members' types; the propagation through class-typed members
  was computed and tested, and its general theorem waited on lemmas
  about resolution over a class's implicit constructors. Those landed
  25 October 2026: seven lemmas say which implicit member resolution
  selects for the argument a subobject supplies, `implicit_deleted` is
  the induction over fuel on them, `value_nature_iff` states the result
  for every class whose special members are the rules' own
  (`implicitClass`), and `deletion_propagates` is the one-step form per
  kind, the move kinds through the copy member since a deleted
  defaulted move member is not a candidate. The definition of a
  reference member changed on the way: a `const` member of class type
  counts, since it deletes the assignment too, and the definition reads
  the subobjects so that a base falls under the same clause. The
  theorem assumes the declarations well-formed (`subobjectsWellFormed`),
  a property of the program's shape. Eleven emitted trait cases observe
  the propagation and the fallback, and the compilers agree. One correction to the
  plan's own statement: a `const` member without an initializer deletes
  the default constructor too ([class.default.ctor]/2, through
  [dcl.init.general]/7), so value nature fails for a reference or a
  `const` member alike. Stage 4, trait-judgements, landed the same day:
  `Overload/Traits.lean` with `Program.trait` for every `Trait`,
  `trait_is_resolution`, `is_convertible_eq_ics`, and forty emitted
  trait cases against the compilers' own traits, all in agreement with
  GCC 15 and Clang 24, `is_trivially_copyable` of a class with a deleted
  copy constructor and a defaulted move constructor among them. Two
  departures. The constraint oracle answers an `Atom`, expression or
  trait, so the environment a program defines answers traits from the
  program and `inheritance_erasure` takes the trait oracle as a
  parameter, the same on both sides, since `is_base_of` sees erasure.
  `is_invocable` of a class callee was residue for a day: the call on an
  object is resolved above the environment, and the trait would need the
  environment that answers it. On 25 October 2026 `Env.fullWithin` took
  it on as it takes a requires-expression, one level down
  (`Program.traitAbove`, `objectInvoke` in `Overload/Requires.lean`):
  `invocable_class_iff_call` is the trait as the call on the object,
  `nothrow_invocable_class_invocable` the nothrow form refining it, and
  `full_invocable_class` the environment's answer.
  Eighteen emitted cases, a hidden and an inherited call operator, an
  ambiguous call, a constrained call operator and one constrained on
  the trait itself among them, agree with GCC 15 and Clang 24. Surrogate
  call functions followed the same day: the call on an object resolves
  over the class's call operators with their implicit object parameter
  and its surrogates, the argument list led by the implied object
  argument ([over.call.object]/2, /3, [over.match.funcs.general]/2 to
  /4; `Program.surrogates`, `objectCandidates`, `impliedObject`,
  `Decl.withImplicitObject`), and `is_invocable` through a surrogate
  with it. Two corrections to the conversion sequences on the way: a
  conversion function yielding a reference is a candidate for binding
  one ([over.match.ref]/1), and its call is an lvalue or xvalue as its
  return type says ([expr.call]/15, `conversionResult`). Eleven emitted
  cases agree with both compilers. What stays with the residue is
  conversion functions declared in a base class, for sequences and
  surrogates alike, and the fragment's want of class template members,
  which a specialization callee inherits: phase 15 is the plan for it. Stage
  5, requires-expressions, landed the same day: `Constraint.conceptId` and `Constraint.requires`,
  `Decl.conceptDef`, `Program.normalize` and `normalizeDecl` applied by
  `Program.call` to its candidates, `Overload/Requires.lean` with
  `requirementsHold`, `Env.full` and the three order theorems, and nine
  emitted cases, the refined concept selected over the one it refines
  among them, all in agreement with GCC 15 and Clang 24. Four
  departures. A requires-expression's calls are resolved above the
  environment, so `Env.full` answers them with the base environment
  below it, one level deep. The requirement-parameter-list is not
  modelled: a requirement names its arguments' types, an lvalue
  reference for an lvalue. Compound and nested requirements waited on
  the return type of the function selected, and landed 25 October 2026:
  `Decl.function` carries a return type, `Program.expression` is what an
  expression requirement's expression is once valid, `decltype((E))` by
  [expr.call]/15 and [dcl.type.decltype]/1 and whether it is potentially
  throwing by [except.spec]/6, `Requirement.compound` holds its
  expression, an optional noexcept-specifier and an optional
  return-type-requirement, `Requirement.nested` a constraint-expression
  without a requires-expression written in place
  (`Constraint.NestedExpr`, since the two types would otherwise be
  mutually inductive, which the derived instances and the `induction`
  tactic do not support), and `Env.full` answers requires-expressions to
  the program's depth rather than one level, so a nested-requirement's
  concept may itself be a requires-expression. `compound_eq_simple_nested`
  is the paragraph's own equivalence, `{ E } -> C<As...>;` as
  `E; requires C<decltype((E)), As...>;`, with `compound_eq_simple` and
  `compound_invalid_eq_simple` for the forms without a
  return-type-requirement and for an invalid expression, and
  `compound_noexcept_throwing` for the noexcept-specifier. Nine emitted
  cases agree with GCC 15 and Clang 24. One residue: whether a braced
  initialization is potentially throwing, so `{ T{} } noexcept;` is
  soft, hence `false` (`decisions.md#trait-residue`). The always-failing
  requirement, ill-formed no diagnostic required, is not checked; GCC 15
  and Clang 24 diagnose it, which two cases met before their failures
  were made to depend on the argument (`findings.md`). Stage 6,
  instance-value-nature, landed the same day:
  `Overload/Typeclass/ValueNature.lean` with `instance_shape_regular`,
  `reference_member_instance`, `copy_constraint_shields`,
  `refinement_normalizes`, `refinement_selects` and
  `member_probe_accurate`, with `member_requirement_iff_call` on the
  Standard side, and seven emitted cases, all in agreement with GCC 15
  and Clang 24. `Program.structural` now looks at members too. Stage 7,
  type-system-docs, closed the phase: this status, the guide, the
  obligations, the findings, the citation index, and `make
  drift-check-current`, which reports three more editorial drifts
  (`findings.md`). [expr.prim.req.compound]/1 and
  [expr.prim.req.nested]/1 joined the in-scope list on 25 October 2026,
  with [expr.call]/15, [dcl.type.decltype]/1 and [temp.param]/9, when
  compound and nested requirements landed.
- Phase 13 is closed, 24 October 2026, planned and landed the same day,
  on its exit criterion: every law a headline theorem of the encoding
  rests on is named and listed by `#owes`, and the headline theorems of
  lookup owe none; the library's object concepts subsume one another by
  normalization (`regular_refines`); the superclass-coherence obligation
  is a theorem with its law as hypothesis (`superclass_coherence_owed`).
  Semantic requirements are named, cited statements nothing decides;
  modelling is satisfaction plus hypotheses, with the verdict of
  [res.on.requirements]/2 for a satisfied concept not modeled; the
  library's concepts are transcribed with their laws; the typeclass laws
  are named. The plan, the cross-reference against N5054 and the stages
  are
  [below](#phase-13-semantic-requirements-what-satisfies-and-what-models).
  Settles semantic-requirements. Stage 2, semantic-requirements,
  landed the same day: `Semantic`, `Decl.semantic`, `Program.laws`
  through a concept's body, `Laws`, `Program.models` with
  `models_satisfies`, `Program.conceptUses`, `Program.modelVerdicts`
  with `IllFormedNdr.satisfiedNotModeled`, `satisfied_not_modeled_verdict`,
  the example of [concepts.equality]/8 as a program, and `#owes`, which
  reports that `coherence` and `stability` owe no law
  (`Overload/Models.lean`). Stage 3, library-concepts, landed the same
  day: `Overload/Concepts.lean` with the library's concepts as a program
  of `conceptDef`s and `semantic`s over the traits of phase 12 and a
  residue atom for each expression the fragment lacks,
  `Trait.isNothrowDestructible` equal to `is_destructible` by
  [class.dtor]/6 (`nothrow_destructible_eq`), `same_as_symmetric`,
  `regular_refines`, `regular_invocable_semantic_only` and
  `regular_laws`, and two emitted cases, the `copy_constructible`
  overload selected over the `move_constructible` one at a flat class
  and the move-only class taking only the latter, in agreement with
  GCC 15 and Clang 24. Two departures: a concept-id takes a fixed number
  of arguments, so `constructible_from` and `invocable` are stated for
  one argument type after the first; and the large normal forms are
  decided in the kernel (`decide +kernel`), which the audit shows
  resting on `propext` alone.
  Stage 4, typeclass-laws, landed the same day:
  `Overload/Typeclass/Laws.lean` names the Functor, Applicative and
  Monad laws and the superclass agreement as `Semantic`s on the
  encoding's concepts, `monad_laws` lists the eight modelling Monad
  needs, `superclass_coherence_owed` is the undiagnosable row as a
  theorem, with the verdict naming the law when unclaimed and none when
  claimed, and `shape_without_laws` gives an instance with the shape and
  no law every law as a verdict; one emitted case agrees with GCC 15 and
  Clang 24. One departure: that `coherence`, `stability`,
  `call_stability`, `inheritance_erasure` and `superclass_identity` owe
  no law is an audit, `#owes` in `Overload.lean` and a test, not a
  theorem, as `#audit` is.
  Stage 5, semantic-docs, closed the phase: the guide, the obligations
  with the slugs and the semantic-requirements section, this status,
  `citations.md` with every in-scope paragraph covered, and `make
  drift-check-current`, which reports the five known editorial drifts
  and no other.
- Phase 14 is closed, 24 October 2026, planned and landed the same day
  in three stages: virtual functions, exception specifications,
  aggregates. Each extends the
  special member judgements of phase 12 with one new fact about
  declarations and the traits that rest on it, and the third corrects
  the model's class value to the aggregate's element list and
  separates `T{}` from `T t;`. The plan, the cross-reference against
  N5054 and the stages are
  [below](#phase-14-virtual-functions-exception-specifications-and-aggregates).
  Settles virtual-fragment, exception-specification-fragment and
  aggregate-fragment.
  Stage 1, virtual-functions, landed 24 October 2026:
  `Overload/Virtual.lean`, with `Virt` on `Decl.function` and on a
  destructor's `SmfDecl`, the virtual functions a class's objects have
  as its final overriders, overriding by signature, polymorphic and
  abstract classes, the inherited virtual destructor, and
  `virtualsWellFormed` for `final` and `override`. Triviality, standard
  layout and emptiness take the no-virtual-functions conjunct;
  `is_constructible`, `is_convertible` and `Program.call` refuse an
  abstract class by value, on the normative rules [basic.def]/5,
  [dcl.fct.def.general]/2 and [expr.call]/7 that the note
  [class.abstract]/3 points to; `is_polymorphic`, `is_abstract` and
  `has_virtual_destructor` are computed. The theorems
  polymorphic-not-trivial, abstract-not-constructible,
  override-is-correspondence and virtual-destructor-inherited are
  proved, with `abstract_polymorphic`, `overrides_iff` and the draft's
  note on an invisible virtual function as an example; on the encoding,
  `virtual_instance_costs` and `abstract_instance_by_reference`.
  Twenty-five emitted cases agree with GCC 15 and Clang 24, and `make
  drift-check-current` reports one more editorial drift, [class.virtual]/2
  (`findings.md`). One departure from the plan: `Virt` has an `override`
  value the plan did not list, since without it [class.virtual]/5 has
  nothing to check.
  Stage 2, exception-specifications, landed 24 October 2026: `noexcept :
  Option Bool` on `Decl.function`, `FunctionTemplate`, `UserConv` and
  `SmfDecl`, `noexcept : Bool` on `Ty.fn`, which deduction compares
  ([except.spec]/3), and `throwingInit` on a member for a default member
  initializer that may throw. `Program.throwingWithin` is the implicit
  exception specification of [except.spec]/7 to /9 through the operation
  resolution selects for each subobject, beside `trivialWithin` and
  shaped like it; `Program.throwing` of a user-declared member is its
  specifier, the implicit rule for a destructor or a defaulted member
  without one, and potentially throwing otherwise. Ten traits join, the
  whole `is_nothrow_` family with `is_nothrow_convertible`,
  `is_nothrow_invocable` of a function type and `is_nothrow_swappable`
  through `std::swap`'s specification ([utility.swap]/4), each the base
  trait and the operations invoked known not to throw ([except.spec]/6);
  `is_nothrow_destructible` is now the real rule and `destructible`
  refuses `~X() noexcept(false)`. `virtualsWellFormed` checks
  [except.spec]/5 for member functions. The theorems nothrow-propagates
  and implicit-noexcept-from-subobjects are proved,
  `nothrow_destructible_eq` is restated for programs whose destructors
  carry no `noexcept(false)`, and the draft's example of [except.spec]/5
  is reproduced; on the encoding, `instance_nothrow` and
  `nothrow_copy_constraint`. Twenty-six emitted cases agree with GCC 15
  and Clang 24. Two departures from the plan: the implicit rule is a
  judgement beside `trivialWithin`, not a field of `Facts`, since
  deletion never consults it; and `nothrow_destructible_eq` is restated
  rather than retired, as the theorem it always was.
  Stage 3, aggregates, closed the phase, 24 October 2026:
  `Overload/Aggregate.lean`, with `aggregate` by [dcl.init.aggr]/1 on the
  declarations, `elementsWith`, `braceInit` for `T{args}`, aggregate
  initialization with `{}` for the elements left out and a reference
  element without an initializer a failure, value-initialization for a
  non-aggregate `T{}` ([dcl.init.list]/3), `parenAggregateInit` for
  `T(args)` when no constructor is viable ([dcl.init.general]/15), which
  `constructible` now reaches, and `implicitLifetimeClass`. The class
  value is restated: `Program.elements`, bases then members, is what a
  `Val.obj` lists, `uniqueValue` is `Option Val`, some only for a class
  whose elements are all classes with one value, and
  `conversion_identifies` and `value_route_identifies_converted` take
  the class's one value as a hypothesis; a converting constructor's
  result for a class with scalar elements is the environment's
  (`decisions.md#value-typing`). `Constraint.Requirement.braceInit` is
  the simple requirement `T{args};`, and `default_initializable` has its
  three conjuncts, `destructible`, `requires { T{}; }` and `T t;`. Two
  traits join, `is_aggregate` and `is_implicit_lifetime`. The theorems
  aggregate-elements-are-value, brace-init-differs-from-default-init and
  paren-aggregate-constructible are proved, with `aggregate_iff_declarations`;
  on the encoding, `instance_is_aggregate`. Twenty emitted cases agree
  with Clang 24 and GCC 16, and fifteen with GCC 15: libstdc++ 15 has no
  `is_implicit_lifetime`, a library gap recorded in `findings.md` and
  `differential/known-disagreements.txt`. Every in-scope paragraph of
  the phase is covered, [class.dtor]/6 by the note's own theorem, and
  `make drift-check-current` reports the six known editorial drifts and
  no other. Settles virtual-fragment, exception-specification-fragment
  and aggregate-fragment.

- Phase 15 is planned, 25 October 2026, and no stage has landed. Class
  templates get bases and members, a specialization gets the template's
  member declarations with its arguments substituted when it is looked
  into, member lookup and the call on an object are keyed by type, and
  the encoding's derivation base is declared as the class template it
  is, with the operation object's constraint resolved as the member call
  it is rather than answered by an oracle. The plan, the cross-reference
  against N5054 and the stages are
  [below](#phase-15-class-templates-and-their-members). Settles
  class-template-members.

## Target theorems

Sixty-one theorems carry the results. A theorem that fails is recorded with
its counterexample and is a finding, not a setback.

| Theorem | Statement | Phase |
|---|---|---|
| determinism | The same program and query always give the same outcome. | 4, 5 |
| mandate-inertness | Adding a Mandate to a candidate never changes which candidate is selected. It can only turn a selection into an ill-formed program. | 2, 5 |
| constraint-promotion | Turning a Mandate into a Constraint removes that candidate where the Mandate fails, so the result moves to the next best, to no match, or to ambiguity. Where the Mandate holds, the outcome is unchanged unless the larger constraint changes partial ordering, which it can. Restated 17 October 2026 (`findings.md`). | 5 |
| sfinae-requires | An `enable_if` encoding and a requires-clause with the same condition give the same viable set. They differ where ordering consults subsumption, and in the step that checks the condition, which decides whether a hard error in the function type is reached. Restated 17 October 2026 (`findings.md`). | 3, 5 |
| subsumption-sound | Subsumption is a preorder and implies satisfaction-implication, up to hard errors in checking the subsumed constraint. The converse fails, with a witness. | 3 |
| coherence | For a ground type, canonical lookup yields at most one instance or reports ambiguity. It never chooses silently. | 6 |
| stability | Adding an instance changes lookup only at types the new instance matches, and there only to the new instance or to ambiguity. | 6 |
| separability | The instance selected is invariant under the choice of conversion ranking. | 5 |
| inheritance-erasure | When every use takes instances at their deduced exact type, replacing derivation between instance types with composition plus retrieval changes no outcome. | 6 |
| superclass-coherence | The Functor derived from a stronger instance, such as `derive_functor<M>`, behaves as the canonical Functor instance where one exists. This is extensional equality of the operations, since the two are different types and so different template arguments. | 6 |
| termination | Lookup terminates under the restriction chosen in termination-condition. | 6 |
| divergence-separation | If two translation units resolve an instance differently, every function whose behaviour depends on that instance has a different identity in the two units. Expected to hold when the instance is a template argument of the function, and to fail when lookup happens inside a body. Fails too for an instance passed as a reference to the lookup variable, which is the canonical route. Restated 17 October 2026 (`findings.md`). | 8 |
| member-transfer | The operation object's call is viable, not viable or ill-formed exactly as the member call through the instance is. The object adds nothing and loses nothing. Added 18 October 2026, from the library audit (`findings.md`). | audit |
| arity-disjoint | An operation object whose `operator()`s differ by arity is stable as one with a single `operator()`, when each puts its lookup default after a parameter a shorter call cannot deduce. Added 18 October 2026. | audit |
| registry-verdicts | A registry tested by completeness has the verdicts of a variable-template lookup, at the same uses, under [temp.constr.atomic]/3 where the test's answer changes. Added 18 October 2026. | audit, 8 |
| algorithm-transfer | An algorithm over an instance whose constraint is the conjunction of its member calls answers as those calls do, in the order written, and is accurate when they are. Added 18 October 2026, from the algorithm probes (`probes.md`). | algorithm |
| dispatch-styles | For one ordered candidate list, the constraint-exclusion, if-constexpr and priority-tag encodings select the same candidate. They differ in whether having no candidate is a soft or a hard failure, and in which conditions are checked: priority tags check all of them. Restated 17 October 2026 (`findings.md`). | 5, 6 |
| redeclaration-inert | A corresponding redeclaration of a function or function template changes no call. Added 20 October 2026. | 9 |
| inner-hides-outer | An unqualified search finds nothing past the first enclosing scope that binds the name. Added 20 October 2026. | 9 |
| object-suppresses-adl | When unqualified lookup binds the callee to an object, the candidate set is that object's call operators, whatever the associated namespaces declare. This makes the `hothers` hypothesis of `call_stability` a theorem for the object design, and a counterexample for a free-function design. Added 20 October 2026. | 9 |
| member-hiding | A derived class's declaration of a name hides every base declaration of it, regardless of signature or constraint. Reproduces the library's hidden constrained member (`findings.md`). Added 20 October 2026. | 9 |
| dependent-call-verdict | A dependent call whose definition and instantiation contexts miss a better-matching external-linkage overload in an associated namespace is ill-formed, no diagnostic required; the verdict cannot arise when the callee is bound to an object. Added 20 October 2026. | 9 |
| entity-identity | The lookup variable's declarations across units declare one entity, by correspondence and linkage. Added 20 October 2026. | 9 |
| narrowing-is-representability | For a constant source, an integral conversion narrows exactly when the value is not representable in the target. Added 21 October 2026. | 10 |
| conversion-shields-call | A conversion failure of an explicit or default template argument is soft and precedes every later step's hard error. Added 21 October 2026. | 10 |
| slicing-identifies | For a base-typed class value parameter, a derived value and the base's own value determine the same specialization. Added 21 October 2026. | 10 |
| reference-keeps-identity | For a reference parameter, the parameter denotes the argument's object, so a derived instance is never identified with its base. Added 21 October 2026. | 10 |
| conversion-invisible-to-deduction | A user-defined conversion between two class types changes no deduced binding: a parameter deduced from its argument is viable at the source type only as it would be without the conversion ([temp.deduct.call]/4). Added 23 October 2026. | 11 |
| conversion-loses-rank | Where a user-defined conversion is the only route to an overload naming a concrete type, a template viable by the identity beats it ([over.ics.rank]/2), and two such overloads reachable by different conversions are indistinguishable. Added 23 October 2026. | 11 |
| converted-argument-temporary | A user-defined conversion yields a prvalue: an lvalue reference parameter to non-const is not viable for it, a reference constant parameter refuses it, and a class-typed value parameter identifies every source that converts to one value. Added 23 October 2026. | 11 |
| explicit-never-implicit | An explicit constructor or conversion function is no candidate for copy-initialization, so it forms no implicit conversion sequence at a call argument or a candidate initializer. Added 23 October 2026. | 11 |
| instantiation-points | A dependent call referenced before a later overload of its name means different things at its two points of instantiation, which is ill-formed, no diagnostic required; a callee bound to an object has one meaning at every point. Added 22 October 2026. | 9 |
| value-nature | For a class that declares no special member function, every defaulted special member is non-deleted exactly when no member, through class-typed members likewise, is of reference type or `const` type; a pointer member deletes nothing. Added 24 October 2026; proved for flat classes the same day (`value_nature_flat`), and in general on 25 October 2026 for every class whose special members are the rules' own through its subobjects (`value_nature_iff`). | 12 | 12 |
| deletion-propagates | A member or base whose class has a deleted or inaccessible corresponding special member deletes the enclosing class's defaulted one, through any depth ([class.default.ctor]/2, [class.copy.ctor]/10, [class.copy.assign]/7, [class.dtor]/7). Added 24 October 2026; proved 25 October 2026 (`deletion_propagates`) for a subobject whose class's special members are the rules' own, the move kinds through the copy member's deletion since a deleted defaulted move member is not a candidate. | 12 |
| compound-is-simple-nested | A compound-requirement with a return-type-requirement is the simple-requirement followed by the nested-requirement of the immediately-declared constraint for `decltype((E))`, and one without is the simple-requirement ([expr.prim.req.compound]/1, [temp.param]/9). Added 24 October 2026; proved 25 October 2026 (`compound_eq_simple_nested`, `compound_eq_simple`, `compound_invalid_eq_simple`). | 12 |
| class-callee-invocable | `is_invocable` of a class callee holds exactly where the call on the object, over its call operators and surrogates with `declval<Fn>()` the implied object argument, is viable and well-formed ([meta.rel]/3, [func.require]/1, [over.call.object]/1 to /3); the environment one level above the program answers it, as it answers a requires-expression. Added and proved 25 October 2026 (`invocable_class_iff_call`, `full_invocable_class`); first stated as the member-call requirement of `operator()`, which the surrogates of the same day made false in general. | 12 |
| surrogate-call-functions | A conversion function to a pointer or reference to function gives a surrogate call function; a call operator beats a surrogate on the implied object argument, which it binds by the identity where the surrogate needs the conversion; two surrogates no argument tells apart make the call ambiguous ([over.call.object]/2, /3). Added and shown by computation 25 October 2026 (`surrogate_example`, `operator_beats_surrogate`, `surrogates_ambiguous`); a general theorem that the implicit object parameter is inert for a class whose call operators are all `const` is owed. | 12 |
| trait-is-resolution | `is_constructible`, `is_assignable` and `is_convertible` are overload resolution over the class's constructors, assignment operators and conversions with the usable-candidate check, so a trait's answer is the call's ([meta.unary.prop]/9, [meta.rel]/6, [over.match.general]/4). Added 24 October 2026; proved the same day (`trait_is_resolution`, `is_convertible_eq_ics`). | 12 |
| requires-soft-is-false | A requirement that fails in the immediate context makes the requires-expression `false`, checked in lexical order and stopping at the first decider; a failure outside it is a hard error ([expr.prim.req.general]/5). Added 24 October 2026; proved the same day (`requires_soft_is_false`, `requires_false_stops`, `requires_hard_stops`). | 12 |
| copy-constraint-shields | A member constrained by copy-constructibility of its callable fails softly at a callable whose copy constructor is deleted, where the body's copy would be a hard error: the callable-copying rule as a theorem. Added 24 October 2026; proved the same day (`copy_constraint_shields`). | 12 |
| refinement-normalizes | The normal form of a refined concept contains its superclass concept's atoms with the identity mapping, so the refinement subsumes by normalization alone ([temp.constr.normal]/1). Added 24 October 2026; proved the same day (`refinement_normalizes`, `refinement_selects`). | 12 |
| models-satisfies | Arguments that model a concept satisfy it; the converse needs every semantic requirement of the concept's specification, which nothing in the language decides ([res.on.requirements]/1). Added 24 October 2026. | 13 |
| satisfied-not-modeled-verdict | A use whose validity depends on arguments modelling a concept that they satisfy with a law unclaimed is ill-formed, no diagnostic required, and the verdict names the law; a use with every law claimed gets none ([res.on.requirements]/2, /3). Added 24 October 2026. | 13 |
| regular-refines | `regular` subsumes `semiregular`, which subsumes `copyable`, which subsumes `copy_constructible`, which subsumes `move_constructible`, each by normalization of the transcribed bodies ([concepts.object]/1). Added 24 October 2026. | 13 |
| regular-invocable-semantic-only | `regular_invocable` and `invocable` have one normal form, so they are satisfied together, and differ only in the law the first owes ([concept.regularinvocable]/3). Added 24 October 2026. | 13 |
| superclass-coherence-owed | A Monad instance that satisfies the Monad concept and claims no superclass agreement gets the verdict at a use that derives its Functor; one that claims it gets none: the obligations table's undiagnosable row as a theorem. Added 24 October 2026. | 13 |
| polymorphic-not-trivial | No special member of a polymorphic class is trivial, so it is neither trivially copyable nor standard-layout ([class.default.ctor]/3, [class.copy.ctor]/12, [class.copy.assign]/9, [class.dtor]/8, [class.prop]/1, /2). Added 24 October 2026. | 14 |
| abstract-not-constructible | No object of an abstract class is created: `is_constructible` is false for every argument list, and a call selecting a function that takes it by value is ill-formed ([class.abstract]/2, /3). Added 24 October 2026. | 14 |
| override-is-correspondence | A member function overrides a base's virtual one exactly when the declarations correspond; a function of the same name with another parameter list hides and does not override ([class.virtual]/2, /3). Added 24 October 2026. | 14 |
| virtual-destructor-inherited | A class derived from one with a virtual destructor has a virtual destructor, declared or implicit, since prospective destructors correspond ([class.virtual]/1, /2). Added 24 October 2026. | 14 |
| nothrow-propagates | A potentially-throwing destructor of a subobject makes the enclosing class's implicit destructor potentially-throwing, and likewise for the constructors and assignments through the operation resolution selects ([except.spec]/7 to /9). Added 24 October 2026. | 14 |
| implicit-noexcept-from-subobjects | A flat class whose members have non-throwing operations has non-throwing special members, and a destructor without a specifier is non-throwing exactly when its subobjects' are ([except.spec]/4, /8). Added 24 October 2026. | 14 |
| aggregate-elements-are-value | A class value's subobject list is the aggregate's element list, bases then members ([dcl.init.aggr]/2), so template-argument equivalence of class values is elementwise. Added 24 October 2026. | 14 |
| brace-init-differs-from-default-init | For an aggregate with a `const` member and no initializer, `T{}` is well-formed and `T t;` is not, so `default_initializable` is false where `requires { T{}; }` holds ([dcl.init.aggr]/6, [dcl.init.general]/7, [concept.default.init]/1). Added 24 October 2026. | 14 |
| paren-aggregate-constructible | An aggregate with no viable constructor is constructible from a parenthesized list of at most as many arguments as elements, each convertible to its element ([dcl.init.general]/15). Added 24 October 2026. | 14 |
| member-template-arguments | Deduction for a member template of a class template specialization binds the member's own parameters only: it is deduction for the member with the class's arguments supplied as the leading explicit arguments ([temp.mem.func]/2, [temp.mem]/1). Added 25 October 2026. | 15 |
| specialization-members-fixed | The member search of a class template specialization gives the same declarations from every point at or after its point of instantiation, which precedes the first declaration that refers to it, in a program whose class templates' members precede that point ([temp.point]/4, /7, [temp.inst]/3). Added 25 October 2026. | 15 |
| specialization-callee-invocable | `is_invocable` of a class template specialization callee is the call on the object over the specialization's call operators and surrogates, so the class-callee residue closes ([func.require]/1, [over.call.object]/1 to /3). Added 25 October 2026. | 15 |
| argument-reference-deletes | A class template with a member of its parameter's type has deleted copy and move assignment at a reference argument and non-deleted at an object type: value nature is a property of the specialization, decided by the argument ([class.copy.assign]/7, through value-nature-iff). Added 25 October 2026. | 15 |
| operation-constraint-is-member-call | The operation object's constraint, `TC.fmap(declval<F>(), declval<T>())`, is the member call on the instance's value type with the lookup's object as the implied object argument: the environment computes what the typeclass side's oracle assumed, and the accurate-member hypothesis of `fmapObject_member` is discharged by computation ([expr.prim.req.compound]/1, [over.match.funcs.general]/3). Added 25 October 2026. | 15 |
| derivation-base-accurate | The derivation base's `fmap` is constrained by the member call its body makes on `Impl`, so a probe of `fmap` through `derive_functor<Impl>` fails softly exactly where `Impl`'s `fmap` is not viable, and the accurate-members obligation holds by construction for the reduced encoding; an instance type that declares its own unconstrained `fmap` hides it ([class.member.lookup]/3). Added 25 October 2026. | 15 |

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
| argument-conversion | Conversions of template arguments decide viability and are never ranked. The draft's own example is ambiguous between `template<int>` and `template<signed char>` ([temp.deduct.general]/12). | A second, unranked conversion relation for the literal-argument route. Whether a derived instance converts to a base-typed constant parameter is unchecked. Phase 10: it converts, by slicing, and the two name one specialization (`slicing_identifies`); the relation is `ConvertsTo`. |
| rank-precedence | Derived-to-base has Conversion rank ([over.best.ics.general]/7). Conversion comparison comes before template specialization and constraints ([over.match.best.general]/2). | The by-value route is the only one where ranking is live. It is an exact match unless instance types are related by inheritance or conversion. Phase 11 puts the user-defined sequence below both ([over.ics.rank]/2). |

The step-order suspect has support in the draft itself. An example in
[temp.constr.atomic]/3 shows a call made ill-formed by a hard error in a
candidate that a better match would have beaten.

The tie-break entry corrects an earlier guess: equivalent template heads
are not required, only equivalent template parameters, so type-constraints
on placeholders do not disable it.

## Instance inheritance

The hypothesis is that inheritance between instance types is
selection-inert exactly when every use site takes the instance at its
deduced exact type. This is the question tracked as instance-inheritance,
decided 17 October 2026: inheritance is allowed, and what it costs is
harvested as obligations.

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
   that should win by refinement can lose on rank. Confirmed 17 October
   2026 (`rank_beats_refinement`, `leak_rank_*.cpp`): an overload naming
   an Applicative instance type wins at that type and loses to a generic
   template at a Monad instance type derived from it.
2. **Deduction from a derived class.** A function parameter of the form
   `functor_impl<F>` deduces from a class derived from it, and fails if more
   than one base matches ([temp.deduct.call]/4). A derived Applicative
   silently matches Functor-shaped signatures. Confirmed 17 October 2026
   (`derived_class_deduction`, `leak_derived_deduction_*.cpp`): a Monad
   instance type derived from `derive_functor<I>` matches a parameter
   `const derive_functor<I>&`, and stops matching once the derivation is
   replaced by composition.
3. **Two paths to the superclass.** Slicing an Applicative to its base gives
   one Functor and lookup gives another. They agree only if the base is the
   canonical instance, and the explicit-instance routes do not force that.
   Recorded 17 October 2026: in the model the two are different template
   arguments whatever their behaviour (`superclass_identity`).
4. **Constant-parameter conversion.** Whether a derived instance is accepted
   for a base-typed constant template parameter is unchecked, and is a
   candidate for compiler disagreement. Settled 15 October 2026: accepted
   and sliced under C++26 (`probes.md`), so the leak is live. A theorem
   since 21 October 2026 (`slicing_identifies`), with the reference
   parameters the library uses as what closes it
   (`reference_keeps_identity`).
5. **Conversion between instance types.** A converting constructor or a
   conversion function from a Monad instance type to an Applicative
   instance type is the other way to write refinement in the type
   system. Theorems since 23 October 2026, phase 11: deduction never
   applies it (`conversion_invisible_to_deduction`), ranking puts it
   below every standard sequence (`conversion_loses_rank`,
   `converting_sites_ambiguous`), and its result is a temporary, which
   the pinning routes refuse and the value route identifies with every
   other value that converts (`converted_instance_temporary`,
   `value_route_identifies_converted`). The encoding avoids this leak
   by design rather than suffering it: refinement by shape is the
   obligation (`obligations.md`).

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

The algebraic laws of each typeclass were excluded at the start; phase 13
names them as semantic requirements, cited where the Standard states the
kind, with the theorems that owe each listed by `#owes`, and still proves
none. These are the obligations of the mechanism.

Each obligation is classified by how it is discharged:

- **By construction.** The library's design makes violation impossible.
- **Compiler-checked.** Violation is a required diagnostic.
- **Library-checkable.** A concept or `static_assert` can catch it.
- **Undiagnosable.** Violation is ill-formed with no diagnostic required, so
  only convention or tooling stands behind it.

The rows below are the candidates expected to fall out. The last column is
a prediction for the model to confirm or correct. The harvest, with what
the model found, is in [obligations.md](obligations.md).

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
| Refinement by shape: the superclass relation is a concept on the instance's shape and a retrieval function, never an implicit conversion between instance types. | Typeclass author | conversion-invisible-to-deduction, conversion-loses-rank | Library-checkable, a `static_assert` that no instance type converts to another |

The undiagnosable rows are the residual trust base. They are what the
single translation unit axiom hides, and they bear on the comparison with
Concept Maps: explicit opt-in removes accidental syntactic matches but not
these.

## Algorithm-author obligations

Planned 18 October 2026. The obligations above belong to typeclass
authors, instance authors and users of explicit instances. A fourth party
writes an algorithm that needs an Applicative or a Monoid and takes one,
`auto&& app` or a policy parameter. Some obligations carry over to that
author unchanged, since the algorithm is one more operation object over an
instance. Others come from where the algorithm sits, between a caller and
an instance it did not choose. Each question below is sized by the
algorithm probes (`probes.md`) at beman.transpose `30a707d`.

The weighing is for accident, not malice. A gap matters by what an
ordinary mistake does. Worst is a program that compiles and gives a wrong
answer. Next is a check that says yes and a call that then fails; then a
hard error where a clean no was owed. A gap whose cost is only a worse
diagnostic is weighed against what closing it costs and what it forbids.
A case it forbids only matters if the case would otherwise have worked.

### algorithm-constraint-accuracy

Does the algorithm's constraint have to imply its body? It is the
accurate-members obligation again, owed by the algorithm. With a deduced
return type, a weaker constraint makes every check of the call a hard
error. Width: as wide as the members it calls. The library's own
`traverse` and `transpose` objects answer every probe correctly. A
violation is safe, since nothing compiles that should not. It matters
only when someone checks the call, and that is what an algorithm meant to
be built on gets. Cost: a trailing return type or restated constraints.
Restating is close to free when the members are accurate, because the
constraint is the conjunction of the member calls. Recommendation: owe it
for algorithms offered for others to constrain on, not for leaf code. The
Lean side is `algorithm_transfer`, below.

### callable-copying

May a member copy the callable it is given? The probes say the concepts'
witness is a good proxy except on this one axis. The three failures in 88
cells are all the callable being copied: `zip_list` copies into a local,
and the sender copies into its deferred work, which it must do. The silent
one is `zip_list` running a copy of a stateful lvalue callable, so the
caller's object never changes. The Standard's answer for its own
algorithms is the note in [algorithms.requirements]/9: they may copy
function objects freely, and `reference_wrapper` is the way to keep
identity. `std::ref` works through every instance probed. Forbidding
copies would forbid deferred contexts, which cannot hold a reference to the
caller's callable. Recommendation: adopt the Standard's rule. An instance
may copy. An instance that copies says so in its constraint (constructible
from the argument), which turns the sender's yes-then-fails into a clean
no. An algorithm that needs identity passes `std::ref`. Nothing that works
today is lost.

### result-context-formable

Must a member's constraint check that its result context exists?
`invoke` with a `void`-returning callable names `std::optional<void>`, a
hard error. Width: every member whose context cannot hold the result.
Safe, and a plausible accident, since a lambda written for its side effect
returns `void`. Cost: one concept per context. It forbids nothing that
compiles today. Recommendation: fold it into the instance's accurate
members rather than make it a separate obligation.

### instance-coherence

May an algorithm given an instance also reach the canonical one for the
same context? A slip through an operation object, or through `bind`, under
the accumulating object keeps the first error and drops the rest. It
compiles silently. Width: today the only same-carrier pair is
`std::expected`'s two applicatives, and they differ in evidence, never in
whether the result fails. The library keeps a value-changing alternative,
the zip applicative, apart by giving it its own carrier, `zip_list`.
Nothing in the language can check the obligation. Cost of a mechanism:
high, and it would forbid the ordinary use of operation objects inside
algorithms. Recommendation: an algorithm-author obligation by convention,
"take every operation on a context from the object you were given", plus
a typeclass-author obligation, "an alternative instance that changes
values gets its own carrier; one that changes only evidence may share it
as an explicit object". The model has no second instance for one key, so
a theorem would need a modelling decision first. Not planned.

### capability-tests

Can an algorithm ask what an object can do? `monad_object` of the
accumulating object is a hard error, because its `bind` is a
`static_assert` in a deduced body. The accumulating object is the one a
caller passes to `traverse`. So an algorithm generic over applicative and
monad objects, dispatching with `if constexpr (monad_object<P, C>)`, fails
to compile on the object it was meant for. Safe, but it blocks the obvious
dispatch. Cost: replace the `static_assert` with a deleted function,
`= delete("…")` keeping the message, which is a clean no on a check.
Nothing is forbidden. Recommendation: an obligation on typeclass and
instance authors that a refused operation is refused as a constraint, and
an upstream issue for the accumulating `bind`. `traverse`'s own
capability test, `collect`, answers correctly.

### typeclass-refinement

Can a stronger object be used where a weaker one is asked for? No
registered monad object is an applicative object, so `traverse` refuses
`monad<optional>` as a policy, cleanly. No registered object satisfies
both concepts either, so overloads on the two are never ambiguous today.
`monad_object` is not written in terms of `applicative_object`, so a user
object that satisfies both makes such overloads ambiguous. Width: narrow,
since `applicative<C>` is registered wherever `monad<C>` is. Cost:
deriving the Applicative members in `derive_monad` is moderate.
Recommendation: when Monad comes to refine Applicative, write
`monad_object` as `applicative_object && …`. This is the plan's
visible-refinement obligation, which nothing has needed yet. No change
now.

### instance-state

May an algorithm make a fresh instance of the type it is given?
`lifted_monoid` and `kleisli_monoid` do, with `APPLICATIVE_OBJECT{}`. A
stateful object, such as one carrying an allocator, scheduler or log, is
silently not consulted. Every registered typeclass object is empty, so
requiring emptiness costs the library nothing today. It would forbid
stateful policies, which `traverse` already supports by taking the object.
`lifted_monoid` itself is not empty, so the rule cannot extend to monoid
objects, whose state `monoid.hpp` allows. Recommendation: an algorithm
either uses the object it was passed or requires `std::is_empty_v` of the
type it constructs. For `lifted_monoid` and `kleisli_monoid`, holding the
object as a `[[no_unique_address]]` member does both at no cost. Upstream
issue.

### instance-exact-type

Must an algorithm take its instance at its exact type? Yes, as for
operation objects, since members are found by static type. Width: nil in
practice. Spelling a base requires an exposition-only name, and the one
probe through a base reference gives the instance's answer. Recommendation:
fold it into the existing exact-type row; no probe or theorem beyond the
one there.

### Work

1. Done: the probes, `probes.md`, this section and a findings entry.
2. Done. Lean, `Overload/Typeclass/Members.lean`: `algorithm_transfer`, with
   `algorithm_accurate` and `call_order_matters`. An algorithm
   object whose body makes several member calls is viable, not viable or
   ill-formed as the conjunction of those calls is. It is accurate when
   its constraint is that conjunction and each member is accurate. This is
   `member_transfer` generalized, with no new rules. A counterexample to
   witness checking is not planned: the probes put the practical gap on
   one axis, and the model has no copy semantics.
3. Done. `obligations.md` and the paper: an algorithm-author section with
   algorithm-constraint-accuracy, instance-coherence and instance-state.
   On the instance side: callable-copying and result-context-formable,
   folded into accurate members. On the typeclass side: capability-tests.
4. Filed as steve-downey/typeclass#17 to #20: the `zip_list` and sender copies
   (callable-copying), `void` results (result-context-formable), the
   accumulating `bind` (capability-tests), and `lifted_monoid` and
   `kleisli_monoid` (instance-state).

## Phase 9: declarations and where to find them

Planned 20 October 2026. The candidate set of a call is an input to the
model, and `decisions.md#lookup-scope` said name lookup was out of scope.
Several of the model's load-bearing claims are nevertheless claims about
lookup, made in prose with no rule behind them:

- A variable cannot be overloaded, and argument-dependent lookup adds no
  candidates when ordinary lookup finds an object (`obligations.md`,
  `findings.md`). This is the `hothers` hypothesis of `call_stability`,
  met "by construction".
- Member lookup stops at the first class whose scope declares the name,
  the mechanism behind the library's hidden constrained member
  (steve-downey/typeclass#10).
- The lookup variable is one entity in every unit, behind
  `operation_object_not_separated`.
- A function declared twice is two candidates today, and `bestViable`
  reports an ambiguity between a function and itself. The Standard says
  the two declarations correspond and are one entity.

P1787R6, *Declarations and where to find them* (S. Davis Herring, adopted
November 2020, in C++23), is where the vocabulary those claims need was
defined: *corresponds*, *precedes*, *single search*, *unqualified search*,
*lookup set*, *overload set*, *associated entities*, *dependent call*.
Phase 9 transcribes the rules the model leans on, so the prose claims
become theorems with cited rules, and it re-examines every citation the
paper touched.

### What P1787R6 did to the sections the model cites

Measured by diffing each section at the commit that applied the paper
(cplusplus/draft `c7e89270`, 15 November 2020) against its parent and
against the pinned tag `n5054`. Nothing the model cites was changed in
substance; two labels were reworded in ways worth recording.

| Cited section | P1787R6's change | Since then, to N5054 | Bearing |
|---|---|---|---|
| [temp.over.link]/6 sentence 2 (`paramEquivalent`) | Deleted "equivalent" and "functionally equivalent function templates" from this section; they became "corresponding overloads" in [basic.scope.scope]/4. Moved "lookup from the first declaration" to [temp.res.general]/1 (CWG1028). | CWG2603 holistic functional equivalence; P2841R7 bullets for concept and variable-template template parameters; the "constant template parameter" rename. | /6 stands. Correspondence of function templates uses the same equivalence as the gate of [temp.func.order]/8, so stage 1 reuses `paramEquivalent`. |
| [temp.point]/7 (`laterInUnit`) | None. | Itemized 2023; P1306R5 added /8; P3596R3 annex tag. | Stands. |
| [temp.spec.partial.general]/1 sentence 3 (`notReachable`) | "shall be declared before the first use ... in every translation unit" became "shall be reachable from any use"; /2 gained "two partial specialization declarations declare the same entity if ...". | Editorial. | Stands, and is P1787R6's wording. /7, "any reachable partial specializations ... are also considered", is what `Units.reachable` transcribes and should cite. |
| [temp.func.order]/1 | "If a function template is overloaded" became "If multiple function templates share a name". | None. | Not cited. |
| [class.access.base]/4, /5 | The naming class became "the class in whose scope name lookup performed a search that found the member" (CWG952). | None. | /4 stands; the fragment has no member access. |
| [over.match.funcs.general]/8, [over.match.viable], [over.match.best.general], [temp.deduct.*], [temp.constr.*], [temp.type]/2 | None. | P0847R7 and CWG2762 reworded the implicit object parameter in [over.match.funcs.general]/2 to /5. | Stand. |
| [temp.res.general] | Rewrote /1, a name in a template is looked up from where it appears, and folded [temp.nondep] into it. | CWG2720, CWG2810, CWG2746 restructured the IFNDR list of /6. | Not yet cited; stage 5 cites /1. |
| [temp.dep.candidate]/1 | "undefined behavior" became "ill-formed, no diagnostic required"; the candidate-finding sentence moved to [basic.lookup.argdep]/4. | P3596R3 annex tag. | Not yet cited; stage 5's verdict. |

### The rules to transcribe, as they stand in N5054

Paragraph numbers are counted from `\pnum` in the pinned text, as the
drift check counts them. "Since" names the commits between the paper and
the pin that changed the paragraph's substance.

| Rule | N5054, abbreviated | Since | Counterpart |
|---|---|---|---|
| [basic.scope.scope]/2 | A declaration inhabits the immediate scope at its locus; its names are bound to it in its target scope. | CWG3097, contracts. | A scope on each declaration. |
| [basic.scope.scope]/4 | Two declarations correspond if they introduce the same name, unless one is a type and the other a variable or function, or each is a function or function template and they do not declare corresponding overloads: the same parameter-type-list and equivalent trailing requires-clauses, or corresponding signatures and equivalent template-heads. | P0847R7, CWG2603 (/3, corresponding signatures). | `Decl.corresponds`. |
| [basic.scope.scope]/6 | Two declarations potentially conflict if they correspond and denote different entities; ill-formed when a name in one scope is bound to two such declarations, one preceding the other. | P2169R4. | `Program.conflicts`. |
| [basic.scope.pdecl]/1 | The locus of a declarator is immediately after it. | None. | Position in the unit. |
| [basic.lookup.general]/1 | Lookup associates a use with a set of declarations; none found is ill-formed; all functions or function templates form an overload set; otherwise, not all the same entity is ambiguous and ill-formed. | None. | `LookupResult`. |
| [basic.lookup.general]/2 | A declaration precedes a program point in the same unit if its locus is before it. The module bullets are out of the fragment. | P2615R1. | `precedes`. |
| [basic.lookup.general]/3 | A single search in a scope for a name from a point finds the declarations that precede the point to which the name is bound in that scope. | None. | `singleSearch`. |
| [basic.lookup.unqual]/2, /3 | An unqualified search in S includes S; if nothing is found, the unqualified search in S's parent. Unqualified name lookup is an unqualified search in the immediate scope. Using-directives are out of the fragment. | Editorial. | `unqualifiedSearch`, `unqualifiedLookup`. |
| [basic.lookup.argdep]/1 | Argument-dependent lookup applies when unqualified lookup finds no class member, no block-scope function, and no declaration that is not a function or function template. | None. | `adlApplies`. |
| [basic.lookup.argdep]/3 | Associated entities: none for a fundamental type; for a class, the class, its enclosing class and, if complete, its bases; for a class template specialization also those of its type template arguments; pointers see through. | CWG2857, P2996R13, P2841R7. | `associatedEntities`, over `Program.allBases`. |
| [basic.lookup.argdep]/4 | The associated namespaces are the innermost enclosing namespaces of the associated entities; the lookup finds every function and function template declaration of the name found by a search in any of them; for a dependent name, also from each point of the instantiation context. | CWG3186. | `associatedNamespaces`, `adl`; the last sentence in stage 5. |
| [basic.lookup.argdep]/6, example | A call of `f` with an `NS::T` argument finds `NS::f` through the associated namespace although unqualified lookup found nothing. The example's second call, where a block-scope declaration suppresses argument-dependent lookup, is out of the fragment. | None. | A test of the first call. |
| [over.call.func]/3 | In an unqualified call the candidates are the set found by name lookup. | P2996R13. | `callCandidates`. |
| [over.call.object]/1 | For a call on an object of class type the candidates include the function call operators of its class, a search for `operator()` in its scope. | None. | `Program.callOperators`, `objectCandidates`. |
| [over.call.object]/2 | For each non-explicit conversion function of the class to a pointer to function, a reference to pointer to function or a reference to function of `(P1, ..., Pn)` returning `R`, the surrogate call function `R call-function(F, P1, ..., Pn)` is a candidate. | None. | `Program.surrogates`, the class's own conversion functions; those of a base class are out. Added 25 October 2026. |
| [over.call.object]/3 | The argument list is the implied object argument followed by the call's arguments; a call operator compares it against its implicit object parameter, a surrogate against its first parameter. | None. | `impliedObject`, `Decl.withImplicitObject` ([over.match.funcs.general]/2 to /4), `Program.objectCallAt`; the example as `surrogate_example`. Added 25 October 2026. |
| [class.member.lookup]/3 to /6 | The declaration set of a name in a class is a single search in its scope; if non-empty, done; otherwise the lookup sets of the direct bases are merged, with the hiding and ambiguity rules; an invalid set is ill-formed. | CWG2582, CWG2642. | `lookupSet`, `memberSearch`. |
| [temp.dep.general]/2 | A dependent call is an unqualified-id called with a type-dependent argument; its name is looked up at the point of instantiation in both the definition and the instantiation contexts. | None. | `Decl.dependentCall`. |
| [temp.res.general]/1 | A name in a template is looked up from where it appears. | Editorial. | The definition context. |
| [temp.point]/1, /7 | The point of instantiation of a function template specialization follows the namespace-scope declaration that refers to it; the end of the unit is another; two points with different meanings are ill-formed, no diagnostic required. | As above. | `Decl.refersTo`, `Program.instantiationPoints`, and the verdict `laterCandidate` (`pointVerdict`). |
| [module.context]/5, /7 | During instantiation the instantiation context holds the point of instantiation; otherwise a point's context is itself. | None. | `Program.dependentLookup`, the lookup from the first point. |
| [temp.dep.candidate]/1 | A dependent call that would be ill-formed, or find a better match, had the lookup considered every external-linkage function declaration in the associated namespaces of every unit, is ill-formed, no diagnostic required. | None. | `IllFormedNdr.betterMatchElsewhere`. |
| [temp.spec.partial.general]/7 | When the primary template name is used, any reachable partial specializations are also considered. | None. | Cite on `Units.reachable`. |
| [basic.link]/3, /4, /8 | A non-template const variable has internal linkage unless inline; a variable, function or template at namespace scope otherwise has external linkage; two declarations declare the same entity if they correspond, have the same target scope, and both have external linkage. | P2788R0, CWG2872. | `linkage`, `sameEntity`. |
| [basic.def.odr]/16 | A definable item with definitions in several units: the same tokens, names denoting the same entity; otherwise ill-formed, a diagnostic required only for named modules. | Restructured 2023, CWG3093. | The rule `operation_object_not_separated` reports. |

Out of the fragment, and said so in the decision: using-directives and
using-declarations, inline and unnamed namespaces, block scopes, modules
and reachability by import, friends, splices, parenthesized callees,
conversion-function-ids, explicit object parameters.

### Stages

Each stage is a branch, closed by its theorems building under the
citation lint, the layering lint and the audits, with `lake test` green
and `citations.md` regenerated. Standard-side modules use neutral names;
the encoding's theorems go under `Typeclass`. The syntax is settled by
`decisions.md#scope-syntax`: a scope field on each namespace-scope
declaration, the program still a flat list, lookup a layer in front of
`resolve`, and every existing theorem untouched.

1. [record-phase-nine](#phase-9-declarations-and-where-to-find-them):
   this section, the decisions, `Overload.Std.inScope`. Done 20 October
   2026.
2. [correspondence](#phase-9-declarations-and-where-to-find-them):
   `corresponds` ([basic.scope.scope]/4, over `headsEquivalent`),
   `Program.conflicts` (/6), the overload set with one entry per entity
   ([basic.lookup.general]/1). Theorems redeclaration-inert and
   `overloadSet_pairwise`. The spurious ambiguity is a finding against
   the model. Done 20 October 2026.
3. [scoped-lookup](#phase-9-declarations-and-where-to-find-them): the
   scope field; `precedes`, `singleSearch`, `unqualifiedSearch`,
   `unqualifiedLookup`, each as relation and function. Theorem
   inner-hides-outer. The emitter renders namespaces. Done 20 October
   2026.
4. [argument-dependent-lookup](#phase-9-declarations-and-where-to-find-them):
   `associatedEntities`, `associatedNamespaces`, `adl`, `adlApplies`,
   `callLookup` and `callAt` ([over.call.func]/3), fed to `Program.call`.
   Theorems object-suppresses-adl and `free_function_admits_adl`. Done
   20 October 2026. The typeclass side's `call_stability` over the
   computed candidates, with `hothers` discharged, and the move of the
   "no other lookup on the name" row of `obligations.md` from "by
   construction" to "by theorem", go with member lookup, once the
   operation object is an object with call operators.
5. [member-lookup](#phase-9-declarations-and-where-to-find-them): members
   as functions scoped in a class; `lookupSet` with the merge rule,
   `memberSearch`, `callOperators` ([over.call.object]/1), which is what
   a call of the operation object resolves over. Theorems member-hiding
   and `ambiguous_bases_example`; the library's hidden constrained
   member reproduced (`unconstrained_member_hides_constrained`), and the
   encoding's `call_stability` restated through the object with
   `hothers` discharged (`call_stability_object`). The member call at
   the operation object's constraint stays an oracle, since a
   constraint's probe is an expression; `Program.memberCallAt` computes
   a member call on the fragment's members. Done 20 October 2026.
6. [dependent-call-verdict](#phase-9-declarations-and-where-to-find-them):
   `Decl.dependentCall`, with its position as the definition context and
   the unit's end as the instantiation context; the verdict of
   [temp.dep.candidate]/1 beside the three of phase 8. Theorems
   `late_adl_overload_verdict` and `object_design_no_adl_verdict`; the
   [temp.res.general]/1 example, `f(t)` at `E` finding the later `f(E)`
   through the instantiation context, as a theorem and an emitted case.
   The example's non-dependent `f(1)` converts `int` to `char`, which
   the model's ranking lacks, so it is not emitted. Done 20 October
   2026.
7. [entity-identity](#phase-9-declarations-and-where-to-find-them):
   `Decl.linkage` and `sameEntity` with the linkage condition
   ([basic.link]/4, /8); the verdict `odrMismatch` for [basic.def.odr]/16
   at a lookup two units instantiate differently, and the theorem that
   it never comes first (`odr_verdict_implies_verdict`), so
   `operation_object_not_separated` cites a rule. Done 20 October 2026.
8. [lookup-differential](#phase-9-declarations-and-where-to-find-them):
   emitter support for namespaces, class members and objects, member
   calls and dependent calls, each added with its stage; twenty-two
   cases compiled with GCC and Clang, all in agreement. The verdicts are
   not compiler-checkable and are theorems only. Done 20 October 2026.
9. [lookup-docs](#phase-9-declarations-and-where-to-find-them): the
   guide, the obligations table, findings, this status, the drift check
   against the draft's main. Done 20 October 2026.
10. [instantiation-points](#phase-9-declarations-and-where-to-find-them):
    [temp.point]/1, the paragraph stage 6 left to the end-of-unit point.
    `Decl.refersTo` is a namespace-scope declaration that refers to a
    dependent call's specialization; `Program.instantiationPoints` is
    the point after each such declaration and the unit's end, each
    once, and the call's lookup runs from the first ([module.context]/5).
    A call that resolves differently at two of its points is the sixth
    verdict, `IllFormedNdr.laterCandidate` ([temp.point]/7, sentence 4).
    Theorems `later_function_verdict` (the draft's [temp.res.general]/1
    program with `h` moved before `void f(E);`: not viable at the first
    point, `f(E)` at the end), `pointVerdict_unreferenced` (no referring
    declaration, one point, so every earlier program reads as before)
    and `object_design_one_meaning`. The emitter renders a referring
    declaration as an alias of the call's type, and asserts the same
    selection at it and at the unit's end; GCC and Clang fix the meaning
    at the first point, as the model does (`findings.md`). Done 22
    October 2026.

Known hazards for the implementation: an omitted trailing default field
in a Lean pattern elaborates to the default value, not a wildcard, so
every existing match on a declaration gets an explicit placeholder and a
guard checks that a namespaced function is seen; `Candidate.index` stays
the position among the declarations lookup found, with
`callAt_eq_call_global` keeping every existing case's numbers; the P3606
perfect match ranges over the found list, which for an object call is
its non-template call operators.

## Phase 10: template arguments and their conversion

Planned 21 October 2026. A constant template argument in the model is a
structural value, `Ty.value`, and the only check an explicit argument
gets is `kindMatches`: a value for a constant parameter, a type for a
type parameter, with the parameter's declared type ignored. A default
argument is formed and bound as it is. The declared types are formed by
`parameterListStep` and discarded. So `template <signed char> f`
accepts `f<1000>`, a `template <bool>` accepts `f<2>`, and a base-typed
class parameter accepts a derived value unchanged, which makes
`X<derived>` and `X<base>` different specializations where the Standard
says they are the same. The draft's own example,
[temp.deduct.general]/12, is the first of these, and `citations.md`
listed it and [temp.arg.nontype]/1 and /3 as in scope with no
counterpart.

The conversion is what [temp.arg.nontype] specifies after P2308R1,
*Template parameter initialization* (adopted November 2023, draft commit
`97ca5cf3`): for a non-class type the argument is a converted constant
expression of that type, which admits integral promotions and
non-narrowing integral conversions ([expr.const.const]/8,
[dcl.init.list]/7); for a class type a temporary `constexpr T v = A;` is
introduced and the parameter's value is `v`'s, so a derived value is
sliced ([temp.arg.nontype]/3 to /5). That rule is behind the
constant-argument probe of `probes.md`, where Clang accepts and slices
and GCC applies the pre-P2308 text, and behind leak 4 of
`decisions.md#instance-inheritance`. Phase 10 makes both theorems with
cited rules, and gives the argument-conversion suspect above its
"second, unranked conversion relation".

### The rules to transcribe, as they stand in N5054

Paragraph numbers counted from `\pnum`, as `make drift-check` does, and
checked against the eel.is anchors for [temp.arg.nontype]: /1 the
invented declaration, /2 the converted constant expression, /3 the
temporary, /4 the class type, /5 the value of P, /6 pointers and
references, /7 and /8 examples. [temp.arg.nontype] is unchanged since
P2308R1 apart from the title and cross-reference edits.

| Rule | N5054 text (abbreviated) | Model counterpart |
|---|---|---|
| [temp.arg.general]/1 | The type and form of each template-argument shall match the type and form of the parameter. | `kindMatches`, cited. |
| [temp.names]/13 bullets 3, 4 | A template-id is valid only if each argument matches its parameter and substitution of each argument into the following parameters succeeds. | `explicitStep`: the declared type of parameter `i` is substituted with the earlier explicit arguments before the conversion. |
| [temp.deduct.general]/2 sentence 1 | If the template-id is not valid, type deduction fails. | A conversion failure is a soft outcome of `explicitStep`. |
| [temp.arg.nontype]/1 | `T x = E;` shall satisfy the constraints of a constexpr definition; if T has a placeholder the parameter's type is deduced from it; a deduced type not permitted for a constant parameter is ill-formed. | Placeholder: the parameter's type is the argument's own, no conversion. The permitted-type check is [temp.param]/12 on the deduced type, at the program level. |
| [temp.arg.nontype]/2 | If T is not a class type, A shall be a converted constant expression of type T; the value of P is A as converted. | `convertedConstant`. |
| [temp.arg.nontype]/3 | Otherwise `constexpr T v = A;` is introduced. | The class cases of `convertArg`: `v` is A when A's class is T, the T base subobject of A (`Program.subobject`) when A's class derives from T, a failure otherwise. |
| [temp.arg.nontype]/4 | For a class type T, a template parameter object exists, template-argument-equivalent to v; ill-formed if the initialization is ill-formed, not constant, or not equivalent. | The fragment's values are constant and `Val.Equivalent` is equality (`Val.equivalent_iff`), so the object's value is `v`: a theorem, not a rule. |
| [temp.arg.nontype]/5 | Otherwise the value of P is that of v. | The binding recorded for the parameter is the converted value. |
| [temp.arg.nontype]/6 | A reference or pointer parameter shall not refer to a temporary. | A `.value` for a reference parameter is a failure; a `.ref` binds. |
| [expr.const.const]/8 | A converted constant expression: implicitly converted, constant, with only the listed conversions, among them integral promotions and integral conversions other than narrowing, and direct reference binding. | `convertedConstant` admits exactly promotion and non-narrowing integral conversion on the fragment's values; a `.ref` binds directly. |
| [dcl.init.list]/7 bullet 4 | Narrowing: from an integer type to an integer type that cannot represent all the values of the original type, except where the source is a constant expression whose value after integral promotions will fit into the target type. | `Narrowing` and `narrowing`, with `narrowing_iff`; `narrowing_constant`: for a constant source, narrowing is exactly the value not being representable. |
| [lex.icon]/3 | The type of an integer literal is the first of int, long int, long long int in which its value can be represented. | `Val.sourceType`. |
| [basic.fundamental]/1, /2, /4 | The signed and unsigned integer types and their ranges; widths are implementation-defined. | `integerTypes`, LP64 (`decisions.md#integer-widths`). |
| [temp.param]/11, /12 | A constant template parameter's type is structural, or contains a placeholder; structural: scalar, lvalue reference, or a literal class whose bases and members are all public and structural. | `Ty.hasPlaceholder` (/11); `Program.structural` (/12), a program-level check on the type a placeholder deduces, outside deduction. |
| [temp.type]/1 bullet 3 | Two template-ids are the same if the parameter values determined by their constant arguments are template-argument-equivalent. | `sameSpecialization`: identity through the converted values. Leak 4 as a theorem. |
| [temp.type]/2, reference bullet | Reference values are equivalent if they refer to the same object. | Already `Val.Equivalent` and `Ty.ref`; `reference_keeps_identity`. |
| [temp.deduct.general]/12 | `f<1000>(0)` OK; `f<1>(0)` ambiguous, not narrowing. | `@[std example]` theorem and emitted case. |

Out of the fragment, recorded in `decisions.md#value-typing`:
floating-point values, pointers and pointers to members, arrays,
enumerations, unions, closure types, user-defined conversions and
converting constructors (the fragment has no expressions),
braced-init-lists, `decltype(auto)` parameters, and the typing of
deduced values ([temp.deduct.type]/20 requires the type of a deduced
`i` to equal the parameter's type in the specialization; the model's
values carry no type, so deduced values pass through unconverted).

### Design

The conversion runs in the two steps where template arguments enter the
bindings, so that `deduceTemplate`'s chain and every theorem about it
are unchanged apart from one new `env` argument: `explicitStep env head
explicit` converts each explicit argument against the parameter's
declared type substituted with the earlier explicit bindings
([temp.names]/13 bullets 3 and 4), and `defaultsStep` converts the
formed default (a default template argument is an initializer-clause
for the same invented declaration, [temp.arg.nontype]/1). A failed
conversion is soft, like a wrong kind today. `convertArg` is total and
never hard; its cases, in order, are the constructors of `ConvertsTo`:
a type for a type parameter; a placeholder anywhere in the declared
type, identity; a dependent declared type, identity until
`parameterListStep` forms it; an integer type, `convertedConstant`; a
class value of the parameter's class, identity; a class value of a
derived class, the base subobject through `Env.subobject`; an lvalue
reference and a `.ref`, identity. `Env` gains that one oracle,
`subobject`, computed by `Program.subobject` with the fuel pattern of
`derives`, so erasure's induction carries over. Structural types stay
out of the deduction path: an `Env.structural` oracle would need a
second congruence hypothesis, and erasing a protected base turns a
non-structural class structural, so `inheritance_erasure` could not
discharge it. `Program.structural` is a program-level predicate.

### Stages

1. [record-phase-ten](#record-phase-ten), docs only: this section, the
   status, the decision entries, `Overload.Std.inScope`.
2. [integer-arguments](#integer-arguments): `Overload/Arguments.lean`
   with the integer types and their ranges, the literal's type,
   `Ty.hasPlaceholder`, narrowing as relation and function with
   `narrowing_iff` and `narrowing_constant`, and `convertedConstant`.
3. [class-arguments](#class-arguments): `Program.subobject`,
   `Env.subobject`, the full `convertArg` with `ConvertsTo`,
   `convertArg_iff`, `convertArg_not_hard`, the simp lemmas and
   `convertArg_congr`, `tpo_value`; the derived-to-base probe as a
   guard.
4. [deduction-conversion](#deduction-conversion): `explicitStep env` and
   `defaultsStep` convert; `kindMatches` cited; the downstream proofs
   re-established, with `explicitStep_congr`, `subobject_erase`,
   `convertArg_erase` and the weakest new hypothesis on the congruence
   lemmas; `temp_deduct_general_12_example`,
   `conversion_soft_shields_call`, `explicitStep_types`.
5. [argument-identity](#argument-identity): `sameSpecialization`,
   `slicing_identifies`, `reference_keeps_identity`,
   `Program.structural`; the typeclass side's restatement on
   `valueRoute` and `pinTemplate`; the emitted cases, with the sliced
   derived value a known disagreement for GCC.
6. [argument-docs](#argument-docs): the guide, the obligations, the
   findings, this status, `citations.md`, `make drift-check-current`.

## Phase 11: user-defined conversions

Planned 23 October 2026. The lower model forms two implicit conversion
sequences, the identity and derived-to-base, and binds a reference
directly or not at all (`Overload/Ranking.lean`). That is what the
typeclass encoding needs, and the general theory was put out of scope
at the start. The question the model cannot answer as it stands is why
the encoding has no converting constructors between instance types, and
whether it should. A Monad instance that converts implicitly to an
Applicative instance looks like a way to write refinement in the type
system. The encoding writes refinement as a concept on the instance's
shape and a retrieval function, `derive_functor<M>`, and takes instances
at their deduced type. Phase 11 adds user-defined conversion sequences
to the Standard side, so that the reasons are theorems and the lower
model answers questions about calls wider than the encoding's.

Four rules do the work. A user-defined conversion is not among the
three differences deduction tolerates between the deduced and the actual
argument type ([temp.deduct.call]/4), so a conversion between instance
types fires at no deduced parameter, which is every generic algorithm.
A user-defined conversion sequence is worse than every standard
conversion sequence ([over.ics.rank]/2), so a generic template beats an
overload naming the converted-to type, and two such overloads reachable
by different conversions are indistinguishable ([over.ics.rank]/3, the
user-defined bullet). The result of a conversion is a prvalue: a
reference binds a temporary ([dcl.init.ref]/5), a reference constant
parameter refuses it ([temp.arg.nontype]/6), and a class-typed value
parameter copy-initializes from it ([temp.arg.nontype]/3), so every
source that converts to one value names one specialization
([temp.type]/1). An explicit constructor or conversion function is no
candidate for copy-initialization ([over.match.copy]/1,
[over.match.ctor]/1, [class.conv.fct]/4), and argument passing is
copy-initialization ([dcl.init.general]/13), so an explicit conversion
fires nowhere an instance is passed. This is the mirror of inheritance
leak 2: derivation is visible to deduction and diverges from refinement
one way, conversion is invisible to deduction and diverges the other.

Casts stay out. An explicit conversion is an expression, and the
fragment has none (`decisions.md#expression-depth`). What `explicit`
does is modelled: the initialization context, copy or direct, is a flag
on the initialization rather than a syntax.

### The rules to transcribe, as they stand in N5054

Paragraph numbers counted from `\pnum`, as `make drift-check` does.
[over.best.ics.general] has thirteen paragraphs in N5054, with the
ambiguous conversion sequence at /12; [over.ics.rank]/3 is one
paragraph whose bullets are cited by their subject.

| Rule | N5054 text (abbreviated) | Model counterpart |
|---|---|---|
| [over.best.ics.general]/1, /6 | An implicit conversion sequence converts an argument to the parameter's type; for a parameter that is not a reference it models copy-initialization of the parameter from the argument. | `Program.ics` forms the sequence in the copy-initialization context. |
| [over.best.ics.general]/3 | A well-formed sequence is standard, user-defined, or ellipsis. | `Ics`: `.standard` or `.userDefined`; the ellipsis sequence is out of the fragment. |
| [over.best.ics.general]/4 | When the target is the first parameter of a constructor or the object parameter of a conversion function that is a candidate by [over.match.copy] or [over.match.conv], user-defined conversion sequences are not considered. | The first standard conversion sequence of a user-defined sequence is formed by the standard cases of `Program.ics` alone; `ics_one_user_defined`. |
| [over.best.ics.general]/7 | Identity for the same class, derived-to-base for a derived class, of Conversion rank. | `baseConv`, cited. [over.ics.user]/4 says the same from the other side: these are given Exact Match and Conversion rank although a constructor is called. |
| [over.best.ics.general]/9 | Only standard conversion sequences convert to the implicit object parameter. | The member call in `Overload/Members.lean` converts the object by the identity; unchanged. |
| [over.best.ics.general]/12 | More than one well-formed sequence is the ambiguous conversion sequence, ranked as a user-defined sequence indistinguishable from any other; a selected function that uses it makes the call ill-formed. | `Ics.ambiguous`; `Program.call` turns a selection whose parameter uses it into an ill-formed call, beside the access check. |
| [over.ics.user]/1, /2 | A user-defined conversion sequence: a standard sequence to the constructor's first parameter or the conversion function's object parameter, the conversion, then a second standard sequence to the target, which includes any reference binding. | `Ics.userDefined first via second`. |
| [over.ics.user]/3 | Through a conversion function template specialization, the second standard sequence has Exact Match rank. | Out of the fragment: no conversion function templates (`decisions.md#user-defined-conversions`). |
| [over.ics.rank]/2 | A standard conversion sequence is better than a user-defined one. | The first tier of `better`, above the present rank comparison. |
| [over.ics.rank]/3, user-defined bullet | U1 is better than U2 when they contain the same constructor or conversion function and U1's second standard sequence is better. | A tier on `.userDefined`; sequences through different conversions are indistinguishable. |
| [over.ics.rank]/4 | Exact Match, Promotion, Conversion. | `ConvRank`, unchanged: Promotion needs arithmetic arguments. |
| [over.ics.ref]/1 last sentence, /2 | A reference bound directly to the result of a conversion function is a user-defined sequence whose second sequence is the binding; a reference not bound directly converts the argument to the referenced type, conceptually copy-initializing a temporary. | `Program.ics` on a reference parameter: direct binding as today, else the sequence to the referenced type with the binding recorded as to a temporary. |
| [over.ics.ref]/3 | No sequence binds an lvalue reference other than to const to an rvalue. | `canBind`, cited; the converted temporary now reaches it. |
| [dcl.init.ref]/5 | A reference-compatible lvalue binds directly; for class types not reference-related, user-defined conversions by the rules for copy-initialization, then the temporary. | The reference cases of `Program.ics`; conversion functions returning references are out of the fragment. |
| [dcl.init.general]/13, /14 | Argument passing is copy-initialization; a parenthesized initializer, a cast or functional notation is direct-initialization. | `Init`: `.copy` or `.direct`. A call's arguments and the candidate initializer are `.copy`; `.direct` appears only as the contrast in `explicit_never_implicit`. |
| [dcl.init.general]/15, last copy-initialization bullet | The user-defined conversions from the source to the destination are enumerated by [over.match.copy] and the best is chosen by overload resolution; an ambiguous choice is ill-formed. | `Program.userConversions`, the candidates; `Program.ics` picks the best by `resolve` over the one argument, and more than one best is `.ambiguous`. |
| [class.conv.general]/4 | At most one user-defined conversion is implicitly applied to a value. | `ics_one_user_defined`, from [over.best.ics.general]/4. |
| [class.conv.ctor]/1 | A constructor that is not explicit specifies a conversion from its parameter types to its class. | `Decl.converting cls (.constructor param explicit)`: a single-argument converting constructor, declared for a ground class. |
| [class.conv.fct]/2, /4 | A conversion function specifies a conversion from its class to the type named; an explicit one is considered only for direct-initialization. | `Decl.converting cls (.function target explicit)`. The note of /3, never invoked to the same class or a base, is the order of the cases of `Program.ics`. |
| [over.match.copy]/1 | Copy-initialization of a class T: the non-explicit constructors of T, and for a class-typed initializer the non-explicit conversion functions to T or a class derived from T. | `Program.userConversions p .copy t src`. |
| [over.match.ctor]/1 | Direct-initialization: all the constructors; otherwise the non-explicit ones. | `Program.userConversions p .direct t src` keeps the explicit constructors. |
| [over.match.conv]/1 | Initialization of a non-class type from a class type: the non-explicit conversion functions whose type converts to T by a standard sequence; explicit ones for direct-initialization. | The non-class target cases of `Program.userConversions`; in the fragment the standard sequence is the identity. |
| [over.match.viable]/4 | A viable function has an implicit conversion sequence for each argument. | `viable`, cited; it now sees user-defined sequences through the ranking. |
| [temp.deduct.call]/4 | Three differences are allowed between the deduced A and A: cv-qualification under a reference, pointer conversions, a derived class. | `deduceParam`, unchanged, which is `deduction_ignores_conversion`. |
| [temp.deduct.general]/5, convertibility | Non-dependent parameters are checked for convertibility. | `Env.convertible`, answered by the new `ics` in `Env.ofProgram`. |
| [temp.arg.nontype]/3 | `constexpr T v = A;` is introduced. | `Program.candidateInitializer`, the environment's `initializer` oracle: the base subobject through the standard sequence, the class's one value through a user-defined one. |
| [temp.arg.nontype]/6 | A reference parameter shall not refer to a temporary. | A `.value` for a reference parameter is a failure, cited; the converted result is a value. |

Out of the fragment, recorded in `decisions.md#user-defined-conversions`:
constructor templates and conversion function templates
([over.ics.user]/3, and the dependent explicit-specifier of
[over.match.funcs.general]/8), conversion functions returning a
reference (the lvalue cases of [dcl.init.ref]/5), list-initialization
and aggregates ([over.match.list], the list bullet of [over.ics.rank]/3),
the ellipsis sequence, conversions to non-class types other than the
identity (no arithmetic arguments), virtual conversion functions, and
access to a conversion ([class.conv.general]/2 defers to [class.access];
`Overload/Access.lean` checks bases only, and a private converting
constructor is a later stage if a question needs it).

### Design

- **Declarations.** A conversion is its own declaration, `Decl.converting
  (cls : Ty) (conv : UserConv)`, as an instance and an object are, so the
  flat program and every match on `Decl.class` stand. `UserConv` is
  `.constructor (param : Ty) (explicit : Bool)` or `.function (target :
  Ty) (explicit : Bool)`. The class is ground: the encoding's instance
  types are named classes in the model's programs, and a conversion on
  every specialization of a class template would need a head the
  fragment does not give class templates. `Program.userConversions init
  tgt src` is the candidate list of [over.match.copy]/1,
  [over.match.ctor]/1 and [over.match.conv]/1, filtered by `explicit`
  against `init`.
- **Sequences.** `Ics` replaces `StdConv` as the ranking's `Conv`:
  `.standard s`, `.userDefined first via second`, `.ambiguous`.
  `Program.ics init a t` tries the standard cases first, as today; for a
  class target it then forms one user-defined sequence per candidate,
  the first sequence by the standard cases only
  ([over.best.ics.general]/4), picks the best candidate by `better` on
  the first sequences ([dcl.init.general]/15), and reports `.ambiguous`
  when more than one is best. A reference parameter not bound directly
  converts to the referenced type and binds the temporary: a const
  lvalue reference or an rvalue reference, never an lvalue reference to
  non-const ([over.ics.ref]/2, /3). `IcsForms` is the relation,
  `ics_iff` the agreement, `ics_one_user_defined` the depth bound.
- **Ranking.** `better` gains a tier above the present chain: standard
  beats user-defined and ambiguous ([over.ics.rank]/2); two user-defined
  sequences compare only through the same `via` ([over.ics.rank]/3);
  `.ambiguous` is indistinguishable from every user-defined sequence
  ([over.best.ics.general]/12). `BetterConv` gains the constructors,
  `better_iff` and `better_asymm` are re-established. `Ranking` stays a
  parameter of the core, so `separability` and every phase 5 theorem are
  untouched; only `Program.ranking` changes.
- **The call.** `Program.call` adds one check beside access: a selected
  function whose parameter uses the ambiguous sequence is an ill-formed
  call ([over.best.ics.general]/12).
- **Deduction.** `Env.ofProgram` answers `convertible` from the new `ics`,
  so the convertibility step sees user-defined conversions as
  [temp.deduct.general]/5 does. `deduceParam` and `callStep` do not
  mention `convertible`, so the bindings deduced on a program are those
  deduced on the program with its conversions removed:
  `deduction_ignores_conversion`, an erasure theorem in the style of
  `inheritance_erasure`, with `Program.eraseConversions`.
- **Template arguments.** As planned, `Env` was to gain a second oracle
  for the value of `constexpr T v = A;` through a converting
  constructor, supplied by hand since the fragment has no constructor
  bodies. As built, the one oracle, renamed `Env.initializer`, answers
  the whole of [temp.arg.nontype]/3, and `Env.ofProgram` computes it as
  `Program.candidateInitializer`: a class value in the fragment lists
  its base subobjects and nothing else, so a class has one value
  whichever constructor made it, and the user-defined case needs no
  body (`findings.md`). The other departure: a value for a placeholder
  reference parameter, which phase 10 accepted, is refused, since the
  invented declaration would bind a temporary; `converted_instance_temporary`
  rests on it.
- **Explicit.** `explicit_never_implicit`: `Program.userConversions .copy`
  holds no explicit conversion, so no implicit conversion sequence and
  no candidate initializer goes through one. The `.direct` contrast is a
  guard, not a theorem, since direct-initialization is a syntax the
  fragment has nowhere to put.
- **The encoding.** `Overload/Typeclass/Conversion.lean`: an Applicative
  instance type and a Monad instance type with a conversion from the
  second to the first. `conversion_invisible_to_deduction`: a generic
  algorithm `template <class A> f(const A&)` deduces the Monad instance
  and selects as it would without the conversion. `conversion_loses_rank`:
  beside an overload naming the Applicative instance type, the generic
  template wins at the Monad instance, by [over.ics.rank]/2 before the
  template preference of [over.match.best.general]/2 is reached.
  `converting_sites_ambiguous`: two overloads naming two instance types
  both reachable from a third by conversion are indistinguishable.
  `converted_instance_temporary`: `pinTemplate`'s `const auto&` refuses
  the converted value, and the value route identifies every source that
  converts to one value (`value_route_identifies_converted`).
  `explicit_conversion_dead`: with the conversion explicit, no call site
  in the encoding forms it. Emitted cases in both emitters.

### Stages

1. [record-phase-eleven](#record-phase-eleven), docs only: this section,
   the status, the theorem rows, leak 5, the obligation row, the decision
   entries, `Overload.Std.inScope`.
2. [conversion-declarations](#conversion-declarations): `UserConv`,
   `Decl.converting`, `Init`, `Program.userConversions` with its
   citations, the `Decl` matches in `Scope`, `Names`, `Resolution` and
   `Emit` extended, the renderer for a converting constructor and a
   conversion function.
3. [conversion-sequences](#conversion-sequences): `Ics`, `Program.ics`
   with the user-defined and ambiguous cases and the binding to a
   temporary, `IcsForms`, `ics_iff`, `ics_one_user_defined`; the
   existing standard cases proved unchanged (`ics_standard`), so every
   present case keeps its numbers.
4. [conversion-ranking](#conversion-ranking): `better` on `Ics`,
   `BetterConv`, `better_iff`, `better_asymm`, `standard_beats_user_defined`,
   `Program.ranking` on `Ics`, the ambiguous-sequence check in
   `Program.call`; emitted cases for the rank, the ambiguity, the
   reference to a temporary, and the draft's example of
   [over.best.ics.general]/12.
5. [conversion-deduction](#conversion-deduction): `Env.ofProgram`'s
   `convertible`, `Program.eraseConversions`,
   `deduction_ignores_conversion`; `Program.candidateInitializer` as
   the environment's `initializer`, with the erasure lemmas
   re-established; `explicit_never_implicit`, `conversion_identifies`.
6. [conversion-typeclass](#conversion-typeclass):
   `Overload/Typeclass/Conversion.lean` with the five theorems above,
   the emitted cases, the obligation row confirmed.
7. [conversion-docs](#conversion-docs): the guide, the obligations, the
   findings, this status, `citations.md`, `make drift-check-current`.

## Phase 12: the type system, special member functions and traits

Planned 24 October 2026. The model's types are what deduction needs: a
name, a parameter, `const`, a pointer, the two references, a
specialization and a constant argument (`Ty`). A class is a name with
bases, and since phase 11 its conversions. Every type trait and every
concept the encoding's constraints use is an atomic constraint with a
string for its expression, answered by the environment's oracle
(`Constraint.Oracle`, `decisions.md#expression-depth`). So the model can
say which candidate a constraint selects, and not why the constraint
holds, and nothing it proves about the encoding's concepts rests on
what the concepts say. Phase 12 widens the lower model in three
directions that depend on one another: the type categories of
[basic.types] and the data members of a class; the special member
functions, implicitly declared, defaulted and deleted; and the type
traits and requires-expressions as judgements computed from those, with
the oracle kept for the residue.

The order is forced by dependency. The traits that look like compiler
magic are nearly all questions about special member functions or class
layout. `is_copy_constructible` is overload resolution over the
constructors with the usable-candidate check. `is_trivially_copyable` is
eligibility and triviality of the copy and move members.
`is_standard_layout` is a predicate on members and bases. Modelled
before the special member functions they would be more oracle strings.
The special member functions in turn need data members, since every
deletion rule is a rule about a member or a base subobject. And the
structural traits, `is_same`, `is_reference`, `is_class`, cost nothing
once the type categories are named, and retire half of the oracle at
once.

Two consumers wait on the typeclass side. The
[callable-copying](#callable-copying) obligation says an instance that
copies its callable should say so in its constraint, so the sender's
yes-then-fails becomes a clean no. That is a theorem once
`is_copy_constructible` of a class with a deleted copy constructor is a
judgement and not an oracle answer. The
[typeclass-refinement](#typeclass-refinement) obligation writes
refinement as a concept on the instance's shape. With concept-ids
normalized, the superclass's atoms appear in the refined concept's
normal form with the identity mapping, and the subsumption is computed
where today a test states it as an atomic identity.

The Standard has no words for value and reference semantics as
properties of a type. The nearest are object type and reference type
([basic.types.general]/1, /6). The phase gives the model two
definitions under the author's names, data and codata: an `int` is
data, an `int&` is codata, and a reference member gives the enclosing
class a codata nature. That has an exact rendering in the rules, as a
theorem and not a rule. A reference member without a default member
initializer deletes the defaulted default constructor
([class.default.ctor]/2), and a reference member deletes the defaulted
copy and move assignment ([class.copy.assign]/7); a `const` non-class
member deletes assignment too; and a member or base whose corresponding
special member is deleted deletes the enclosing one
([class.default.ctor]/2, [class.copy.ctor]/10, [class.copy.assign]/7,
[class.dtor]/7). So for a class that declares no special member of its
own, every defaulted special member is non-deleted exactly when no
member, through class-typed members likewise, is of reference type or
`const` non-class type. Pointers mark the limit of the idea. A
pointer's codata aspect is aliasing of what it points to, which is a
question about the object model, and the fragment has no object model.
The type system says a pointer is data: a scalar, trivially copyable,
and it deletes nothing. The scope statement is
`decisions.md#value-nature`, so the model does not promise more.

### The rules to transcribe, as they stand in N5054

Paragraph numbers counted from `\pnum`, as `make drift-check` does. The
trait tables of [meta.unary.cat], [meta.unary.comp], [meta.unary.prop]
and [meta.rel] carry no `\pnum` of their own; each lies in the
paragraph before it by that count, /3, /2, /5 and /3, and a row is
cited there by its template's name. [special] is the section's stable
name in N5054, with [class.mem.special] gone.

| Rule | N5054 text (abbreviated) | Model counterpart |
|---|---|---|
| [basic.types.general]/1, /6 | Types describe objects, references, or functions. An object type is a type that is not a function type, not a reference type, and not cv `void`. | `Ty.isObject`, `Ty.isReference`, `Ty.isFunction`: every `Ty` that is a type is exactly one of the three. |
| [basic.types.general]/7 | Scalar types: arithmetic, enumeration, pointer, pointer-to-member, `nullptr_t`, and cv-qualified versions. Trivially copyable types: scalar types, trivially copyable class types, arrays of such, cv versions. Standard-layout types likewise. | `Ty.isScalar`: the fragment's scalars are its integer types, `bool` and pointers. `Program.triviallyCopyable` and `Program.standardLayout` on a `Ty`, through the class predicates of [class.prop]. |
| [basic.compound]/1 | Compound types: arrays, functions, pointers, references, classes, unions, enumerations, pointers to members. | `Ty.isCompound`. `Ty.fn params ret` is new: the function type of a parameter list and a return type, with `params` a `nil`/`cons` chain. |
| [basic.fundamental]/1, /2 | The signed and unsigned integer types. | `Ty.isIntegral`, from phase 10's `integerTypes`; cited there already. |
| [class.mem.general]/5, /15 | A data member is a non-function member introduced by a member-declarator. A brace-or-equal-initializer of a non-static data member is a default member initializer. | `Member := { name, ty, init : Bool }` on `Decl.class`. The initializer is a flag, since it is an expression. |
| [special]/1 | Default constructors, copy and move constructors, copy and move assignment operators, and destructors are special member functions; the implementation implicitly declares them when the program does not. | `SmfKind`, six constructors; `Program.specialMembers c`, the six with their provenance. |
| [special]/5 | Two special member functions are of the same kind if both are default constructors, both copy or move constructors with the same first parameter type, or both assignment operators with the same first parameter type and qualifiers. | Equality on `SmfKind` and the parameter's `const`; the fragment has no ref-qualifiers. |
| [special]/6 | An eligible special member function is not deleted, has its constraints satisfied, and no other of the same kind with satisfied constraints is more constrained. | `Program.eligible`: not deleted. The fragment's special members carry no constraints, so the other two bullets hold. |
| [special]/7 | A class's potentially constructed subobjects are its direct non-static data members, its non-virtual direct bases and, if not abstract, its virtual bases. | `Program.subobjectsOf c`: members then direct bases; no class in the fragment is abstract or has a virtual base. |
| [class.default.ctor]/1 | If a class has no user-declared constructor, a non-explicit constructor with no parameters is implicitly declared as defaulted. | `Program.implicitDefaultCtor`: suppressed by any user-declared constructor, which in the fragment is a `Decl.converting` constructor or a declared special member. |
| [class.default.ctor]/2 | Defined as deleted if: a reference member has no default member initializer; a `const` member without one is not const-default-constructible; a potentially constructed subobject of class type `M` has no usable candidate for `M`'s corresponding constructor; or a subobject's class has a deleted or inaccessible destructor. | `Program.deleted c .defaultCtor`, four bullets, with [dcl.init.general]/7 and [over.match.general]/4. The variant-member clauses are out. |
| [class.default.ctor]/3 | Trivial if not user-provided and: no virtual functions or bases; no default member initializer; every direct base's default constructor trivial; every class-typed member's trivial. | `Program.trivial c .defaultCtor`. |
| [class.copy.ctor]/1, /2 | A copy constructor's first parameter is `X&` or `const X&` (or volatile forms); a move constructor's is `X&&` or `const X&&`. | `SmfDecl` of kind `.copyCtor` or `.moveCtor` with `constParam`. `volatile` is out. |
| [class.copy.ctor]/6 | Without a user-declared copy constructor, a non-explicit one is declared implicitly; defined as deleted if the class declares a move constructor or move assignment operator, otherwise defaulted. | `Program.implicitCopyCtor`, with the deprecated case kept as the text has it. |
| [class.copy.ctor]/7 | The implicit copy constructor has the form `X(const X&)` if each potentially constructed subobject of class type `M` has a copy constructor taking `const M&`; otherwise `X(X&)`. | `Program.copyParam c`. |
| [class.copy.ctor]/8 | Without a user-declared move constructor, a non-explicit one is declared as defaulted iff the class has no user-declared copy constructor, copy assignment, move assignment or destructor. | `Program.implicitMoveCtor`. |
| [class.copy.ctor]/10 | A defaulted copy/move constructor is defined as deleted if: a potentially constructed subobject of type `M` has no usable candidate for `M`'s corresponding constructor; a subobject's class has a deleted or inaccessible destructor; or, for the copy constructor, a member of rvalue reference type. A deleted defaulted move constructor is ignored by overload resolution. | `Program.deleted c .copyCtor` and `.moveCtor`; `Program.constructors c`, the candidate list, omits a deleted defaulted move constructor. |
| [class.copy.ctor]/12 | Trivial if not user-provided and: no virtual functions or bases; the constructor selected for each direct base is a direct member of the base and trivial; the one selected for each class-typed member is trivial. | `Program.trivial c .copyCtor`, `.moveCtor`, through the constructor `resolve` selects for the subobject. |
| [class.copy.assign]/1, /3 | A user-declared copy assignment operator has one non-object parameter of type `X`, `X&` or `const X&`; a move assignment operator `X&&` or `const X&&`. | `SmfDecl` of kind `.copyAssign` or `.moveAssign`, with `constParam`; the by-value form is out. |
| [class.copy.assign]/2 | Without a user-declared copy assignment operator one is declared implicitly; deleted if the class has a user-declared move constructor or move assignment, else defaulted; of the form `operator=(const X&)` if each direct base and class-typed member has a copy assignment taking `const M&` or `M`, else `operator=(X&)`. | `Program.implicitCopyAssign`, `Program.assignParam c`. |
| [class.copy.assign]/4 | A move assignment operator is implicitly declared as defaulted iff the class has no user-declared copy constructor, move constructor, copy assignment or destructor. | `Program.implicitMoveAssign`. |
| [class.copy.assign]/7 | A defaulted copy/move assignment operator is defined as deleted if the class has: a member of `const` non-class type; a member of reference type; a direct member or base of class type `M` with no usable candidate for `M`'s corresponding assignment operator. A deleted defaulted move assignment is ignored by overload resolution. | `Program.deleted c .copyAssign`, `.moveAssign`; `Program.assignments c` omits a deleted defaulted move assignment. |
| [class.copy.assign]/9 | Trivial, as [class.copy.ctor]/12 for assignment. | `Program.trivial c .copyAssign`, `.moveAssign`. |
| [class.dtor]/2 | Without a user-declared prospective destructor one is implicitly declared as defaulted. | `Program.implicitDtor`. |
| [class.dtor]/7 | A defaulted destructor is defined as deleted if a potentially constructed subobject has class type `M` whose destructor is deleted or inaccessible. | `Program.deleted c .dtor`; the union and virtual-destructor bullets are out. |
| [class.dtor]/8 | Trivial if not user-provided, not virtual, every direct base's destructor trivial and every class-typed member's trivial. | `Program.trivial c .dtor`. |
| [dcl.fct.def.default]/1 | A function definition `= default;` is explicitly defaulted, and shall be a special member function (or a comparison or increment operator). | `SmfBody.defaulted` on a `SmfDecl`. |
| [dcl.fct.def.default]/5 | Explicitly defaulted and implicitly declared functions are defaulted; a defaulted special member that is not eligible is defined as deleted; a function is user-provided if user-declared and not explicitly defaulted or deleted on its first declaration. | `Provenance`: `.implicit`, `.defaulted`, `.userProvided`, `.deleted`. `Program.deleted` is the "defined as deleted" judgement over the defaulted ones. |
| [dcl.fct.def.delete]/1, /2 | A deleted function has a deleted definition or is implicitly defined as deleted. A construct that designates a deleted function is ill-formed; for an overload set only the selected function is referenced. | `SmfBody.deleted`; the usable-candidate check after selection, beside access, as the second sentence says. |
| [dcl.init.general]/7 | A type is const-default-constructible if default-initialization would invoke a user-provided constructor, or it is a class each of whose direct members has a default member initializer or is const-default-constructible and each of whose potentially constructed bases is. | `Program.constDefaultConstructible`. |
| [over.match.general]/4 | Overload resolution results in a usable candidate if it succeeds and the selected candidate is not deleted and is accessible from the context. | `Program.usable`, over the result of `resolve`. `Program.call`'s access check is this rule's second half, cited at last. |
| [class.prop]/1 | A trivially copyable class has at least one eligible copy or move constructor or assignment operator, each eligible one trivial, and a trivial non-deleted destructor. | `Program.triviallyCopyableClass`. |
| [class.prop]/2 | A standard-layout class: no member of non-standard-layout class or reference type; no virtual functions or bases; the same access for all members; no non-standard-layout base; at most one base subobject of any type; all members first declared in one class; no base in `M(S)`, the types at zero offset. | `Program.standardLayoutClass`, the seven bullets on the fragment, where members are public and there are no bit-fields; `M(S)` is the first member's type and its own `M`. |
| [meta.unary.cat]/3 | Exactly one primary type category holds of any type: `is_integral`, `is_pointer`, `is_lvalue_reference`, `is_rvalue_reference`, `is_class`, `is_function` in the fragment. | `Trait` constructors answered by `Program.trait`; `one_primary_category`, a theorem of the table. The categories with no inhabitant in the fragment answer false, cited. |
| [meta.unary.comp]/2 | `is_reference`, `is_object`, `is_scalar`, `is_compound`, `is_fundamental` as compositions. | `Program.trait`, through [basic.types.general]/6, /7. |
| [meta.unary.prop]/5, the table | `is_const`; `is_trivially_copyable` and `is_standard_layout` by [basic.types.general]/7; `is_empty`: a non-union class with no non-static data members, no virtual members or bases, and every base empty; `is_default_constructible` and the copy and move forms as `is_constructible` with `const T&` and `T&&`; `is_assignable<T, U>`: `declval<T>() = declval<U>()` well-formed in the immediate context; `is_copy_assignable` and `is_move_assignable` from it; `is_destructible`; the `is_trivially_` forms: the trait holds and the operation is known to call nothing non-trivial. | `Program.trait` cases. `is_assignable` is `resolve` over `Program.assignments` of the class of `T` with the one argument, then `usable`; non-class assignment is an expression and stays with the residue. |
| [meta.unary.prop]/9 | `is_constructible<T, Args...>` holds iff `T t(declval<Args>()...);` would be well-formed, access checked as from an unrelated context, only the immediate context considered. | `Program.constructible t args`: direct-initialization ([dcl.init.general]/14, `.direct`) resolved over `Program.constructors`, then `usable`. The model's access check is from an unrelated context already. |
| [meta.rel]/3, the table | `is_same`: the same type with the same cv-qualification. `is_base_of`: a base class, private, protected or ambiguous included, or the same non-union class. `is_invocable<Fn, Args...>`: `INVOKE(declval<Fn>(), declval<Args>()...)` well-formed. | `is_same`: equality on `Ty`. `is_base_of`: `derives` or the same class, access ignored as the note says. `is_invocable`: the call on an object (`Overload/Members.lean`) for a class `Fn`, a direct call for a `Ty.fn`. |
| [func.require]/1 | `INVOKE(f, t1, ..., tN)` is `f(t1, ..., tN)` when `f` is not a pointer to member. | `Program.objectInvoke`: for a class callee, the call on the object, over its call operators and surrogates with `declval<Fn>()` the implied object argument ([over.call.object]/1 to /3); answered by `Env.fullWithin` one level down, like a requires-expression. |
| [over.match.funcs.general]/2, /3, /4 | A member function has an implicit object parameter; the context supplies an implied object argument; the parameter is an lvalue reference to cv `X` for a function without a ref-qualifier, `X` the class of which it is a direct member. | `Decl.withImplicitObject`, `const X&` for the fragment's const members; `impliedObject`. |
| [over.match.ref]/1 | For binding a reference to cv1 `T`, the conversion functions yielding an lvalue reference to cv2 `T2`, with cv1 `T` reference-compatible with cv2 `T2`, are candidates. | `Program.userConversions` admits a conversion function by the type it yields with references and `const` stripped; `userSequence` binds or refuses through `conversionResult`. |
| [meta.rel]/6 | `is_convertible<From, To>` holds iff `To test() { return declval<From>(); }` would be well-formed, access as from an unrelated context, the immediate context only. | `Program.convertible from to`: `p.ics .copy` from the argument `declval<From>()` yields, to `To`, a sequence that is not ambiguous and whose conversion is usable. A return is copy-initialization. |
| [temp.constr.normal]/1 | The normal form of a concept-id `C<A...>` substitutes the arguments into `C`'s constraint-expression, then into the parameter mappings of the atoms; any other expression is an atomic constraint with the identity mapping. | `Constraint.conceptId name args`; `Program.normalize`, with `Decl.concept`'s body a `Constraint`. Concept-dependent constraints and folds are out. |
| [temp.constr.atomic]/2, /3 | Identity of atomic constraints; satisfaction, with an invalid substitution in the immediate context as not satisfied. | In scope already. Identity of `.trait q m` and `.requires` is structural equality; `Program.satisfied` on them, soft to false. |
| [expr.prim.req.general]/5 | An invalid type or expression in the immediate context of a requirement, or a violated semantic constraint, makes the requires-expression `false`, not the program ill-formed; checking proceeds in lexical order and stops when the result is determined; a requires-expression that cannot succeed is ill-formed, no diagnostic required. | `Program.requiresSatisfied`, `requires_soft_is_false`, `requires_order`. The always-fails case is a program-level check, like `scopesWellFormed`. |
| [expr.prim.req.simple]/1 | A simple-requirement asserts the validity of an expression. | `Requirement.simple call`: the fragment's expressions are calls, decided by `callAt` as viable and well-formed. |
| [expr.prim.req.type]/1 | A type-requirement asserts the validity of a type. | `Requirement.type t`: a template-id valid by [temp.names]/13, which `explicitStep` decides. A nested type name is out. |
| [expr.prim.req.compound]/1 | A compound-requirement asserts the expression valid and, with a return-type-requirement, the immediately-declared constraint of the type-constraint for `decltype((E))` satisfied; equivalent to a simple-requirement and a nested-requirement. | `Requirement.compound call constraint`: the selected function's `ret` substituted into the type-constraint; `compound_eq_simple_nested`, the paragraph's own equivalence. The noexcept-specifier is out. |
| [expr.prim.req.nested]/1 | A nested-requirement's constraint-expression shall be satisfied by the substituted arguments. | `Requirement.nested c`. |

Out of the fragment: unions and anonymous unions, variant members,
arrays, bit-fields, virtual functions and virtual bases (so no
polymorphic or abstract class, no virtual destructor), inherited
constructors and using-declarations, exception specifications (the
`is_nothrow_` traits), constexpr-suitability and literal types,
aggregates ([dcl.init.aggr], so `is_aggregate` and
`is_implicit_lifetime`), the access of a user-declared special member
(every special member in the fragment is public; `= delete` carries
the idiom a private copy constructor once did), enumerations,
floating-point types and `nullptr_t`, pointers to members, `volatile`,
the by-value copy assignment operator, the ref-qualifier and the
explicit object parameter of [dcl.fct.def.default]/2, `is_swappable`,
`has_unique_object_representations`, layout compatibility, alignment,
concept-dependent constraints and fold expanded constraints, a
requires-expression written in place inside a nested-requirement, and
nested type names in a type-requirement. The noexcept-specifier of a
compound requirement landed with phase 14's exception specifications,
for a call; for a braced initialization it is residue. Recorded in `decisions.md#special-member-fragment`
and `decisions.md#trait-residue`.

### Design

- **Types.** `Ty` gains one constructor, `fn (params : Ty) (ret : Ty)`,
  the function type ([basic.compound]/1), with `params` a `nil`/`cons`
  chain so every proof stays an ordinary `induction`. Deduction treats
  it as it treats `spec`, structurally; the forms `T()` and `T(T)` of
  [temp.deduct.type]/8 are already in scope. The predicates of
  [basic.types.general] are functions on `Ty`: `isObject`, `isReference`,
  `isFunction`, `isScalar`, `isClass`, `isIntegral`, `isCompound`,
  `isConst`, with `removeConst`, `removeReference`, `removeCvref` and
  `addLvalueReference` beside `stripConst`. `Decl.function` and
  `FunctionTemplate` have a return type already (`ret`, defaulting to
  `void`); the compound requirement and `is_invocable_r` read it.
  Adding a constructor to `Ty` touches every deduction induction; the
  cost is paid in stage 2, while it is one constructor and nothing
  depends on it.
- **Members.** A data member is its own declaration after its class,
  `Decl.member cls m`, as a conversion is, with `Member` a name, a type
  and whether it has a default member initializer; `Program.membersOf`
  lists a class's in order. The plan had them as a field of
  `Decl.class`; a separate declaration keeps the flat program and every
  match on `Decl.class`, the reason phase 11 gave for `Decl.converting`. Members are
  public and non-static; a member's type may be a reference, a `const`
  type, a pointer, a scalar or another class. `Program.subobjectsOf` is
  the potentially constructed subobjects ([special]/7). Erasure
  (`Overload/Erasure.lean`) carries members untouched, as it carries
  bases.
- **Special members.** `SmfKind` is the six kinds. A class declares
  special members as `SmfDecl := { kind, body : SmfBody, constParam :
  Bool }` with `SmfBody` one of `.userProvided`, `.defaulted`,
  `.deleted`; `Decl.class` gains `special : List SmfDecl`.
  `Program.specialMembers c` is the set of [special]/1: the declared
  ones, and for each kind not user-declared the implicit one by
  [class.default.ctor]/1, [class.copy.ctor]/6 and /8,
  [class.copy.assign]/2 and /4, [class.dtor]/2, with its parameter form
  by [class.copy.ctor]/7 and [class.copy.assign]/2. `Program.deleted c
  k` is "defined as deleted" for a defaulted member, the bullets of
  [class.default.ctor]/2, [class.copy.ctor]/10, [class.copy.assign]/7
  and [class.dtor]/7, recursive through the subobjects' classes via
  `resolve` over their constructors or assignments and the
  usable-candidate check ([over.match.general]/4), fuel-bounded by
  declaration order as `derivesWithin` is. `Program.trivial c k`
  likewise. `Program.eligible` is non-deletion ([special]/6). The
  relation is `SpecialMember`, the function `specialMembers`, the
  agreement `specialMembers_iff`; `deleted_iff` and `trivial_iff` the
  same for the two judgements. `Program.constructors c` and
  `Program.assignments c` are the candidate lists: the special members
  by signature and the `Decl.converting` constructors, less a deleted
  defaulted move member. `Program.userConversions` draws its
  constructors from `constructors` from here on, so a deleted copy
  constructor is a candidate that resolution may select and the usable
  check then refuses, as [dcl.fct.def.delete]/2 says.
- **Value nature.** `Program.valueNature c`: every special member of
  `c` is defaulted and non-deleted. `Program.referenceMember c`: some
  subobject of `c`, or of a class-typed subobject's class likewise, is
  of reference type or `const` type. `value_nature_iff`: for a class
  whose special members are the rules' own, through its class-typed
  subobjects to any depth (`implicitClass`), `valueNature` holds iff
  `referenceMember` fails.
  `pointer_member_keeps_value_nature`: a pointer member deletes nothing.
  `deletion_propagates`: a member or base of class `M` with a deleted
  corresponding special member deletes the enclosing defaulted one,
  through any depth. These are definitions and theorems; no cited
  sentence states them, and the data and codata names stay in the docs.
- **Traits.** `Trait` is an inductive of the queries the fragment can
  state, with the arity each takes; `Program.trait q args : Subst Bool`
  answers them by the rules above. `Constraint` gains `.trait (q :
  Trait) (mapping : List Ty)` beside `.atomic`, with identity by
  structural equality ([temp.constr.atomic]/2) and satisfaction by
  `Program.trait` on the substituted mapping, an invalid substitution
  in the immediate context giving `false` ([temp.constr.atomic]/3).
  `Constraint.atomic` and the oracle remain for the residue, so every
  existing case stands. `trait_is_resolution`: `is_constructible`,
  `is_assignable` and `is_convertible` are `resolve` plus `usable` over
  the class's candidates with the argument, so the trait's answer is
  the call's; `is_convertible_eq_ics` names the phase 11 sequence.
- **Requires-expressions and concept-ids.** `Constraint` gains
  `.requires (params : List Ty) (reqs : List Requirement)` and
  `.conceptId (name : String) (args : List Ty)`; `Decl.concept`'s body
  becomes a `Constraint`, with the string body kept as `.atomic` for
  the existing cases. `Requirement` is `.simple call`, `.type t`,
  `.compound call constraint`, `.nested c`, where a `call` is a callee
  and argument types over the requirement's parameters, decided by
  `callAt`. `Program.normalize` expands concept-ids
  ([temp.constr.normal]/1), fuel-bounded by declaration order, since a
  concept names only concepts declared before it. Satisfaction of
  `.requires` is in lexical order, a soft failure of any requirement is
  `false`, a hard one is hard ([expr.prim.req.general]/5):
  `requires_soft_is_false`, `requires_order`, `compound_eq_simple_nested`.
  Subsumption (`Overload/Constraint.lean`) runs on the normal form, so
  a refined concept subsumes its superclass's concept-id structurally.
- **The call and the emitter.** `Program.call` gains the usable check
  on the selected constructor of a copy-initialized class parameter,
  beside access and the ambiguous sequence. `Overload/Emit.lean`
  renders members, special member declarations with `= default` and
  `= delete`, and a trait or requires-expression as a `static_assert`
  on the `std::` trait or the concept, so every trait judgement is
  differentially tested against the compilers' own answers.
- **The encoding.** `Overload/Typeclass/ValueNature.lean`:
  `instance_shape_regular`, an instance type with no data members and
  no declared special member has every special member defaulted,
  non-deleted and trivial, so it is trivially copyable and empty;
  `copy_constraint_shields`, a member constrained by
  `is_copy_constructible` of its callable fails softly at a callable
  with a deleted copy constructor, where the body's copy would be a
  hard error, the [callable-copying](#callable-copying) rule as a
  theorem; `reference_member_instance`, an instance type that holds a
  reference is structural for the value route ([temp.param]/12) and
  not assignable, so the two notions do not coincide;
  `nested_reference_instance`, the reference nature reaches an instance
  through two class-typed members, by `value_nature_iff`;
  `refinement_normalizes`, the refined concept's normal form contains
  the superclass's atoms with the identity mapping, so the refinement
  subsumes with no hand-written identity, the
  [typeclass-refinement](#typeclass-refinement) obligation's mechanism;
  `member_probe_accurate`, a requires-expression over a member call
  holds exactly where the call is viable and well-formed, which is the
  accurate-members obligation stated as the Standard states it.

### Stages

1. [record-phase-twelve](#record-phase-twelve), docs only: this
   section, the phase row, the status, the theorem rows, the decision
   entries, `Overload.Std.inScope`.
2. [type-categories](#type-categories): `Ty.fn` with its deduction and
   substitution cases and every induction re-established; the
   predicates and transformations on `Ty`; `Member` and
   `Decl.class.members`, carried through `Scope`, `Names`, `Erasure` and
   `Emit`; `Trait` with the structural queries, `Constraint.trait`,
   identity and satisfaction, `one_primary_category`; emitted cases
   asserting the `std::` traits.
3. [special-members](#special-members): `SmfKind`, `SmfDecl`,
   `Program.specialMembers` with `SpecialMember` and
   `specialMembers_iff`; `deleted` and `trivial` with their relations
   and agreement; `eligible`, `constructors`, `assignments`, `usable`;
   `userConversions` over `constructors`; the usable check in
   `Program.call`; `value_nature_iff`, `pointer_member_keeps_value_nature`,
   `deletion_propagates`; emitted cases with `= default`, `= delete`,
   reference and `const` members.
4. [trait-judgements](#trait-judgements): the remaining `Trait` cases:
   `is_constructible` and its family, `is_assignable` and its family,
   `is_destructible`, `is_convertible`, `is_base_of`, `is_empty`,
   `is_trivially_copyable`, `is_standard_layout`, the `is_trivially_`
   forms, `is_invocable`; `trait_is_resolution`, `is_convertible_eq_ics`;
   emitted cases for each against the compilers' traits.
5. [requires-expressions](#requires-expressions): `Requirement`,
   `Constraint.requires`, `Constraint.conceptId`, `Decl.concept` with a
   `Constraint` body, `Program.normalize`, satisfaction in lexical
   order; `requires_soft_is_false`, `requires_order`,
   `compound_eq_simple_nested`; subsumption over the normal form, with
   the phase 3 theorems re-established; emitted cases with concepts
   and `requires` bodies.
6. [instance-value-nature](#instance-value-nature):
   `Overload/Typeclass/ValueNature.lean` with the five theorems above
   and their emitted cases; the obligation rows confirmed.
7. [type-system-docs](#type-system-docs): the guide, the obligations,
   the findings, this status, `citations.md`, `make drift-check-current`.

## Phase 13: semantic requirements, what satisfies and what models

Planned 24 October 2026. Phase 12 made every constraint the fragment can
state a judgement: a trait is computed, a requires-expression is decided,
a concept-id is expanded. What none of that reaches is the half of a
concept's specification that is not a constraint. [res.on.requirements]/1
says a sequence of template arguments *models* a concept when it
*satisfies* it, which is [temp.constr.decl], and meets all semantic
requirements given in the concept's specification; /2 says a program
whose validity depends on modelling, where the arguments satisfy but do
not model, is ill-formed, no diagnostic required. The library's concepts
each carry such requirements: `copy_constructible` that the copy is
equal to the original and leaves it unmodified ([concept.copyconstructible]/1),
`equality_comparable` that `==` says `true` exactly for equal values
([concept.equalitycomparable]/2), `regular_invocable` that the call is
equality-preserving ([concept.regularinvocable]/1), which is the whole of
its difference from `invocable` (/3). The typeclass laws are
requirements of the same kind: an instance whose `fmap` has the right
shape satisfies the Functor concept, and one whose `fmap` preserves
identity and composition models it. The plan so far excluded the
algebraic laws from the obligations table. Phase 13 brings them in, not
as things proved but as things named: a semantic requirement is a cited,
slugged statement that nothing decides, modelling is satisfaction plus
hypotheses, a theorem that needs a law says so in its statement, and an
audit lists the laws each headline theorem rests on. The verdict of
[res.on.requirements]/2 joins the ill-formed-no-diagnostic verdicts of
`Units`: it is the precise sentence for "the compiler cannot catch this".

Two things the phase does not do. It does not check a law, since the
fragment has no expressions to evaluate and a law is a statement about
values; and it does not encode a law as a decidable property, since that
would be a second, unverified transcription of the same prose. Its value
is that every law has one name, one citation, and a list of the theorems
that assume it.

### The rules to transcribe, as they stand in N5054

Paragraph numbers counted from `\pnum`, as `make drift-check` does. In
the concepts library a concept's definition precedes its first numbered
paragraph, so a body is cited at the paragraph that follows it. The
object concepts are one section, [concepts.object]; [concept.object] is
not a stable name.

| Rule | N5054 text (abbreviated) | Model counterpart |
|---|---|---|
| [res.on.requirements]/1 | `Args` models `C` if `Args` satisfies `C` and meets all semantic requirements given in the specification of `C`. | `Program.models laws c args`: the normal form of `c<args>` satisfied, and every `Semantic` of `c` held by `laws`, an oracle nothing computes. |
| [res.on.requirements]/2 | If the validity or meaning of a program depends on whether arguments model a concept, and the concept is satisfied but not modeled, the program is ill-formed, no diagnostic required. | `IllFormedNdr.satisfiedNotModeled`, the verdict `Program.modelVerdicts` gives at a use where a law is not claimed. |
| [res.on.requirements]/3 | If the semantic requirements of a declaration's constraints are not modeled at the point of use, ill-formed, no diagnostic required. | `Program.conceptUses`: the concept-ids of the selected candidate's constraint, with the deduced arguments substituted, are the uses whose modelling the call depends on. |
| [structure.requirements]/8 | Required operations need not be total functions; some arguments may make the required semantics fail; this does not affect whether a type models the concept. | The `Semantic` docstring: a law is stated on the domain of its expressions; the model's oracle takes it as given. |
| [concepts.equality]/1, /2, /3 | An expression is equality-preserving if equal inputs give equal outputs; the domain of an expression is the inputs for which it is required to be well-defined; equality-preserving expressions are stable. | `Semantic` constants `equalityPreserving` and `stable`, the vocabulary the library's laws are written in. |
| [concepts.equality]/4 | Expressions declared in a requires-expression in the library clauses are required to be equality-preserving unless annotated otherwise. | Each library concept's `Decl.semantic` includes `equalityPreserving` unless the concept's text annotates its expression, as `invocable` does. |
| [concepts.equality]/5, /6 | Which operands an expression may modify; implicit expression variations, required to meet the same semantics. | `Semantic` constants `nonModifying` and `implicitVariations`. |
| [concepts.equality]/8 | A type that meets the stated syntactic requirements of a concept but not the implicit ones satisfies but does not model it. | `@[std example]` theorem: a type satisfying a concept with an unclaimed law gets the verdict. |
| [concept.same]/1 | `same_as<T, U>` subsumes `same_as<U, T>` and vice versa. | `same_as` as a `conceptDef` over `is_same` both ways; `same_as_symmetric`, a theorem of normalization. |
| [concept.derived]/1 | `derived_from<Derived, Base>` is satisfied iff `Derived` is publicly and unambiguously derived from `Base`, or they are the same class. | `derived_from` over `is_base_of` and a pointer conversion the fragment lacks, a residue atom. |
| [concept.convertible]/1, /2 | `convertible_to` requires implicit and explicit convertibility; models only if the two produce equal results and the source is left as stated. | Body over `is_convertible` and a residue atom for the `static_cast`; `Semantic` `convertibleToEqual`. |
| [concept.destructible]/1 | `destructible<T> = is_nothrow_destructible_v<T>`. | `Trait.isNothrowDestructible`, equal to `is_destructible` in the fragment: no declaration has a noexcept-specifier, so a destructor has the exception specification of an implicitly declared one ([class.dtor]/6). |
| [concept.constructible]/1 | `constructible_from<T, Args...> = destructible<T> && is_constructible_v<T, Args...>`. | A `conceptDef`. |
| [concept.default.init]/1 | `default_initializable<T> = constructible_from<T> && requires { T{}; } && is-default-initializable<T>`, where the last is `T t;` well-formed. | A `conceptDef` over `is_default_constructible`, which is `T t;`; `T{}` is value-initialization in the fragment's classes, noted. |
| [concept.moveconstructible]/1 | Body; models only if `T u = rv;` and `T(rv)` equal the value `rv` had, and `rv` is left valid but unspecified. | A `conceptDef`; `Semantic` `moveConstructibleEqual`. |
| [concept.copyconstructible]/1 | Body; models only if the copy equals `v` and `v` is not modified. | A `conceptDef`; `Semantic` `copyConstructibleEqual`. |
| [concept.assignable]/1, /2 | `assignable_from<LHS, RHS>`: `LHS` an lvalue reference, a common reference, and `lhs = rhs` of type `LHS`; models only if the assignment returns `lhs`, leaves `lhs` equal to `rhs`'s value, and treats `rhs` as stated; need not be total. | A `conceptDef` over `is_lvalue_reference`, `is_assignable` and a residue atom for the common reference; `Semantic` `assignableFromEqual`. |
| [concept.swappable]/1, /2, /3, /4 | Exchanging values; `ranges::swap`, with a selected `swap` that does not exchange values ill-formed, no diagnostic required; `swappable<T> = requires(T& a, T& b) { ranges::swap(a, b); }`; the semantics are the customization point's. | A `conceptDef` over a residue atom; `Semantic` `swapExchanges`; /2's verdict is the same verdict at the `swap` use. |
| [concept.booleantestable]/1, /2 | `boolean-testable-impl<T> = convertible_to<T, bool>`; models only if no `operator&&` or `operator||` is found. | A `conceptDef`; `Semantic` `booleanTestableNoLogicalOperators`. |
| [concept.equalitycomparable]/1, /2, /3 | `weakly-equality-comparable-with`, the four comparisons boolean-testable; models only if they share a domain and agree; `equality_comparable<T>` models only if `==` is `true` exactly for equal values; the note that equality preservation makes `==` symmetric and transitive. | A `conceptDef` over a residue atom for the comparison operators; `Semantic` `weaklyEqualityComparable`, `equalityComparableEqual`. |
| [concepts.object]/1, /2, /3 | `movable`, `copyable`, `semiregular`, `regular` as conjunctions; `semiregular` is modeled by types that behave like `int` without `==`, `regular` with it. | `conceptDef`s; `regular_refines`: each subsumes the one before by normalization. |
| [concept.invocable]/1, /2 | `invocable<F, Args...>` by `invoke`, not required to be equality-preserving; a random number generator can model it. | A `conceptDef` over `is_invocable`, with no `equalityPreserving` law. |
| [concept.regularinvocable]/1, /2, /3 | `regular_invocable = invocable`; the call shall be equality-preserving and not modify the function object or arguments; the distinction is purely semantic. | A `conceptDef` with the same body and the law `equalityPreserving`; `regular_invocable_semantic_only`: the two normal forms are equal, so satisfaction agrees and only the laws differ. |
| [class.dtor]/6 | A destructor declaration without a noexcept-specifier has the exception specification of an implicitly declared one. | `isNothrowDestructible` equals `isDestructible` on the fragment. |

Out of the fragment: `common_reference_with` and the common reference
type, `derived_from`'s pointer conversion, the comparison operators and
`ranges::swap` as expressions (each a residue atom in a concept's body,
answered by a case's table), `totally_ordered` and the ordering concepts,
`equality_comparable_with`'s cross-type requirement, `is_nothrow_`
beyond destruction, `predicate` and `relation`, and any law's truth.
Recorded in `decisions.md#semantic-requirements`.

### Design

- **A semantic requirement.** `Semantic` is a slug and a statement, the
  slug kebab-case and named for the question, the statement the
  requirement in words, with the citation on the Lean constant that
  defines it. Nothing decides one: `Laws := Semantic → List Ty → Prop`
  is the oracle, a hypothesis a theorem states. The Standard's are in
  `Overload/Concepts.lean`; the encoding's laws, which the Standard does
  not state, are in `Overload/Typeclass/Laws.lean` with their source in
  the statement. `Decl.semantic concept law` attaches a requirement to a
  concept's specification, its own declaration after the `conceptDef`,
  as a member or a conversion is after its class.
- **Modelling.** `Program.laws c` is the requirements of `c`'s
  specification and, through the concept-ids in its body, of the
  concepts it is defined in terms of: modelling `regular` is modelling
  `semiregular` and `equality_comparable`. `Program.models env laws c
  args` is satisfaction of the normal form of `c<args>` and every law
  held; `models_satisfies` is the one direction the text gives.
- **The verdict.** A case claims laws as it claims atomics, a table
  `claims : List (Semantic × List Ty)`. `Program.conceptUses` takes the
  selected candidate of a call and lists the concept-ids its template's
  constraint-expression names, with the deduced arguments substituted,
  which are the uses the call's validity depends on
  ([res.on.requirements]/3). `Program.modelVerdicts` gives
  `IllFormedNdr.satisfiedNotModeled c args law` for each such use that
  is satisfied with a law not claimed. `satisfied_not_modeled_verdict`:
  a claimed law gives no verdict, an unclaimed one names it; the example
  of [concepts.equality]/8 reproduces as a program.
- **The library's concepts.** `Overload/Concepts.lean` transcribes the
  concepts above as a `Program` of `conceptDef`s and `semantic`s,
  `libraryConcepts`, over the traits of phase 12 and residue atoms for
  the expressions the fragment lacks. `Trait.isNothrowDestructible` is
  added, equal to `isDestructible` by [class.dtor]/6. Theorems:
  `same_as_symmetric`, `regular_refines` (regular subsumes semiregular
  subsumes copyable subsumes copy_constructible subsumes
  move_constructible), `regular_invocable_semantic_only`. Emitted cases
  put two overloads under `semiregular` and `regular` at a class and
  check the more refined is selected, with the residue atoms declared as
  string-bodied concepts in the C++.
- **The audit.** `#owes decl` lists the `Semantic` constants in a
  declaration's closure, as `#rests_on` lists sentences: the laws a
  theorem assumes. `Overload.lean` runs it on the encoding's headline
  theorems, and `coherence` and `stability` owe none.
- **The encoding.** `Overload/Typeclass/Laws.lean` names the Functor,
  Applicative and Monad laws and the superclass-agreement law, which the
  plan's inheritance section calls a law on instance authors, as
  `Semantic`s attached to the encoding's concepts. `superclass_coherence_owed`:
  a Monad instance that satisfies the Monad concept and claims no
  superclass agreement gets the verdict at a use of `as_functor`, and
  one that claims it gets none, which is the obligations table's
  "undiagnosable" row as a theorem. `coherence_owes_no_law` and
  `stability_owes_no_law`: the two headline theorems of lookup mention
  no `Semantic`, checked by `#owes`.
- **The obligations table.** Each row that is a law gains the slug of
  its `Semantic`, and `docs/obligations.md` gains a section listing the
  model's semantic requirements with the theorems that owe each, from
  `#owes`.

### Stages

1. [record-phase-thirteen](#record-phase-thirteen), docs only: this
   section, the phase row, the status, the theorem rows, the decision
   entry, `Overload.Std.inScope`.
2. [semantic-requirements](#semantic-requirements): `Semantic`,
   `Decl.semantic`, `Program.laws`, `Laws`, `Program.models`,
   `models_satisfies`, `Program.conceptUses`, `Program.modelVerdicts`,
   `IllFormedNdr.satisfiedNotModeled`, `satisfied_not_modeled_verdict`,
   the [concepts.equality]/8 example, `#owes`.
3. [library-concepts](#library-concepts): `Overload/Concepts.lean`,
   `Trait.isNothrowDestructible`, `same_as_symmetric`,
   `regular_refines`, `regular_invocable_semantic_only`, emitted cases.
4. [typeclass-laws](#typeclass-laws): `Overload/Typeclass/Laws.lean`,
   `superclass_coherence_owed`, `coherence_owes_no_law`,
   `stability_owes_no_law`, emitted cases.
5. [semantic-docs](#semantic-docs): the guide, the obligations with the
   slugs and the `#owes` section, the findings, this status,
   `citations.md`, `make drift-check-current`.

## Phase 14: virtual functions, exception specifications and aggregates

Planned 24 October 2026. Three parts of the type system that the traits of
phase 12 reach for and the fragment does not have. A virtual function makes
a class polymorphic, takes every special member's triviality with it, and
makes an abstract class one no object can have. An exception
specification is a predicate on every function, explicit or implicit, and
the whole `is_nothrow_` family is one rule over it. An aggregate is what a
class with no user-declared constructor is, and aggregate initialization
is what `T{}` and, since C++20, `T(args)` mean for it, which is also what
the model's class values have been all along: a value is its elements.
Each is a stage, each closes with its own docs and citations, and each
extends the same machinery, the special member judgements of phase 12 and
the resolution they rest on, with one new fact about declarations.

Two corrections come with the third stage. The model's class value,
`Val.obj`, lists base subobjects and nothing else, and phase 11 rested
"one value per class" on it; with data members since phase 12 that is
wrong for a class with a scalar member, and the aggregate's elements,
bases then members ([dcl.init.aggr]/2), are what the value should list.
And phase 13 took `T{}` and `T t;` to be one condition in
`default_initializable`; for an aggregate with a `const` member they
differ, and the stage separates them.

### The rules to transcribe, as they stand in N5054

Paragraph numbers counted from `\pnum`, as `make drift-check` does. The
inherited virtual destructor has no sentence of its own in N5054: a
prospective destructor of a derived class corresponds to a base's and so
overrides it ([class.virtual]/2), which is where the rule now lives.

| Rule | N5054 text (abbreviated) | Model counterpart | Stage |
|---|---|---|---|
| [class.virtual]/1 | A non-static member function is virtual if first declared `virtual` or if it overrides a virtual member function of a base. A class with a virtual member function is a polymorphic class. | `Decl.function` gains `virt : Virt` (`.none`, `.virtual`, `.pure`, `.override`, `.final`); `Program.virtualFunctions c`, `Program.polymorphic c`. | 1 |
| [class.virtual]/2 | `G` in a derived class overrides virtual `F` of a base when the declarations correspond; a final overrider; more than one final overrider is ill-formed. | `Program.overrides`, by `corresponds` from phase 9; `Program.finalOverrider`; the inherited virtual destructor, since prospective destructors correspond. | 1 |
| [class.virtual]/3 | A virtual function need not be visible to be overridden; a function with another parameter list hides and does not override. | `override_is_correspondence`: overriding is correspondence, hiding is the name; `derived_member_hides_base` already covers the latter. | 1 |
| [class.virtual]/4, /5 | Overriding a `final` function is ill-formed; `override` on a function that overrides nothing is ill-formed. | `Program.virtualsWellFormed`, a program-level check like `scopesWellFormed`. | 1 |
| [class.virtual]/12 | A virtual function shall be defined or declared pure; no diagnostic required. | Out: the fragment has no definitions; noted. | 1 |
| [class.abstract]/2, /4 | A pure virtual function; a class with a pure virtual function whose final overrider is pure is abstract; no object of an abstract class can be created except as a subobject. | `Program.abstract c`; `Program.constructible` is `false` at an abstract class; the aggregate and the value route refuse one. | 1 |
| [class.abstract]/3 | An abstract class type cannot be a parameter or return type of a function being defined or called, or the type of an explicit conversion; pointers and references to it can. | A note; the rules it points to are the next three rows. `abstract_by_value_ill_formed`. | 1 |
| [basic.def]/5 | In the definition of an object, its type shall not be an abstract class type. | `Program.constructible` is `false` at an abstract class: `T t(args)` defines an object. `abstract_not_constructible`. | 1 |
| [expr.call]/7 | When a function is called, the type of any parameter shall not be a class type that is incomplete or abstract. | `Program.abstractParameter`; `Program.call` is ill-formed when the selected function has a by-value parameter of abstract type, before any argument's conversion is examined. | 1 |
| [dcl.fct.def.general]/2 | The return type of a function definition shall not be an abstract class type. | `Program.convertible` to an abstract class by value is `false`: the test function of [meta.rel]/6 is a definition. | 1 |
| [class.dtor]/11 | A prospective destructor can be declared virtual and pure. | `SmfDecl` of kind `.dtor` with `virt`. | 1 |
| [class.default.ctor]/3, [class.copy.ctor]/12, [class.copy.assign]/9, [class.dtor]/8 | Trivial only with no virtual functions (and no virtual bases); a destructor trivial only if not virtual. | The "no virtual functions" conjunct of `trivialWithin`, always true until now, becomes `!p.polymorphic c`, and the destructor's `!virtual`. | 1 |
| [class.prop]/1, /2 | Trivially copyable and standard-layout need no virtual functions. | `triviallyCopyableClass` through triviality; `standardLayoutWithin` gains the conjunct. | 1 |
| [meta.unary.prop]/5, rows `is_polymorphic`, `is_abstract`, `has_virtual_destructor`, `is_empty` | A polymorphic class; an abstract class; a virtual destructor; empty needs no virtual member functions. | `Trait.isPolymorphic`, `isAbstract`, `hasVirtualDestructor`; `emptyWithin` gains the conjunct. | 1 |
| [except.spec]/1 | The exception specification is a predicate, potentially-throwing or non-throwing, defined implicitly or by a noexcept-specifier. | `Decl.function`, `FunctionTemplate`, `UserConv` and `SmfDecl` gain `noexcept : Option Bool`, `none` for no specifier; `Program.throwing` decides the predicate. | 2 |
| [except.spec]/2, /3 | `noexcept` without an expression is `noexcept(true)`; in a function type the specifier is the type's exception specification. | `Ty.fn` gains `noexcept : Bool`, part of the type, deduced by equality as the form `T() noexcept(i)` of [temp.deduct.type]/8 allows for a non-dependent `i`. | 2 |
| [except.spec]/4 | A declaration without a noexcept-specifier is potentially throwing, unless it is a destructor or a deallocation function or is defaulted on its first declaration. | `Program.throwing` on a user-provided function: the specifier, or potentially throwing; on a destructor or a defaulted member: the implicit rule below. | 2 |
| [except.spec]/5 | An override of a non-throwing virtual function shall be non-throwing unless deleted. | `Program.virtualsWellFormed` gains the check, joining the two stages. | 2 |
| [except.spec]/6 | An expression is potentially-throwing if it calls a function with a potentially-throwing exception specification, implicitly invokes one, or has a potentially-throwing immediate subexpression. | The fragment's expressions are calls: a call is potentially-throwing when the selected function is; `is_nothrow_invocable` for a function type reads the type. | 2 |
| [except.spec]/7 | An implicitly-declared or defaulted constructor is potentially-throwing iff a constructor selected to initialize a potentially constructed subobject is, or a default member initializer is. | `Program.throwingWithin c k` for the constructor kinds, through `resolveCtor` on each subobject, as `deletedWithin` is; a default member initializer is an expression, so `Member` gains `throwingInit : Bool`. | 2 |
| [except.spec]/8 | An implicitly-declared destructor, or one without a specifier, is potentially-throwing iff a potentially constructed subobject's destructor is. | `Program.throwingWithin c .dtor`; `nothrow_destructible_eq` of phase 13 is restated for programs whose destructors carry no `noexcept(false)`, and `destructible` distinguishes `~X() noexcept(false)`. | 2 |
| [except.spec]/9 | An implicitly-declared or defaulted assignment operator is potentially-throwing iff an assignment it invokes is. | `Program.throwingWithin c k` for the assignment kinds, through `resolveAssign`. | 2 |
| [meta.unary.prop]/5, the `is_nothrow_` rows; [meta.rel]/3, `is_nothrow_convertible`, `is_nothrow_invocable` | Each is the base trait and the operation known not to throw. | `Trait.isNothrow*` answered by the base judgement and `!throwing` of the function resolution selects; `is_nothrow_swappable` by the move operations when no `swap` is declared ([concept.swappable]/2). | 2 |
| [utility.swap]/4 | `std::swap`'s exception specification is `is_nothrow_move_constructible_v<T> && is_nothrow_move_assignable_v<T>`. | `Program.nothrowSwappable`, with a program that declares a `swap` of its own left to the oracle. | 2 |
| [dcl.init.aggr]/1 | An aggregate: a class with no user-declared or inherited constructors, no private or protected direct members, no private or protected direct bases, and no virtual functions or virtual bases. | `Program.aggregate c`: no special constructor declaration, no converting constructor, no protected base, not polymorphic; members are public. | 3 |
| [dcl.init.aggr]/2 | The elements of a class aggregate: the direct bases in declaration order, then the direct non-static data members in declaration order. | `Program.elements c`; `Val.obj c subs` lists them, bases then members, and `candidateInitializer` and `uniqueValue` are restated for classes with members (`decisions.md#value-typing`). | 3 |
| [dcl.init.aggr]/4 | The elements an initializer list explicitly initializes; `{}` explicitly initializes none. | `Program.braceInit c inits`: the first `k` elements from the list. | 3 |
| [dcl.init.aggr]/6 | An element not explicitly initialized is initialized from its default member initializer, else copy-initialized from `{}` if not a reference, else the program is ill-formed. | The rest of `braceInit`: a reference element without an initializer fails; `T{}` for a class with a `const` member succeeds where `T t;` does not. | 3 |
| [dcl.init.list]/3 | List-initialization of an aggregate is aggregate initialization; of a class with a default constructor from an empty list, value-initialization; otherwise its constructors are considered. | `braceInitWithin` at a non-aggregate class: `T{}` and `T{args}` through `resolveCtor`. | 3 |
| [dcl.init.general]/8 | To value-initialize an object: a class by its default constructor, a scalar by zero-initialization; a reference is no object. | `Program.valueInit`, for the elements a parenthesized aggregate initialization leaves out. | 3 |
| [dcl.init.general]/15, the aggregate bullet | If no constructor is viable, the destination is an aggregate class and the initializer is a parenthesized expression-list, each element is copy-initialized from the corresponding expression, more expressions than elements is ill-formed, and the rest from their default member initializers or value-initialized. | `Program.constructible` gains the branch: `is_constructible<Agg, Args...>` holds through the elements when no constructor is viable. | 3 |
| [class.prop]/8 | An implicit-lifetime class: an aggregate whose destructor is not user-provided, or one with a trivial eligible constructor and a trivial non-deleted destructor. | `Program.implicitLifetimeClass`; `Trait.isImplicitLifetime`. | 3 |
| [meta.unary.prop]/5, row `is_aggregate` | `T` is an aggregate type. | `Trait.isAggregate`. | 3 |
| [concept.default.init]/1 | `constructible_from<T> && requires { T{}; } && is-default-initializable<T>`. | The body's three conjuncts become three judgements: `braceInit` for `T{}`, `is_default_constructible` for `T t;`. | 3 |

Out of the fragment: virtual base classes, so the virtual-base bullets of
[special]/7, [class.dtor]/8 and [except.spec]/8 and the unique final
overrider across virtual bases; covariant return types ([class.virtual]/8,
/9); `final` on a class and `is_final`; deallocation functions and the
virtual destructor's lookup of one ([class.dtor]/7 last bullet, /15);
`noexcept` with a dependent expression and the `noexcept` operator; the
throw-expression and the other potentially-throwing expressions of
[except.spec]/6; arrays as aggregates, designated initializers, anonymous
unions and brace elision ([dcl.init.aggr]/3, /5, /7 onward); inherited
constructors; `is_nothrow_swappable_with`. Recorded in
`decisions.md#virtual-fragment`, `decisions.md#exception-specification-fragment`
and `decisions.md#aggregate-fragment`.

### Design

- **Virtual functions.** `Virt` is `.none`, `.virtual`, `.pure`,
  `.override` or `.final`, a field of `Decl.function` and of a
  destructor's `SmfDecl`; `.override` is virtual only through what it
  overrides, so that [class.virtual]/5 is checkable.
  `Program.overrides d b` is correspondence of a derived class's member
  declaration with a base's virtual one; `Program.virtualFunctions c`
  is the declared and the overriding; `polymorphic` is non-empty;
  `finalOverrider c f` walks the derivation; `abstract c` is a pure
  virtual whose final overrider is pure. `trivialWithin` takes
  `!polymorphic` as the conjunct the plan left trivially true, and the
  destructor's `!virtual`; `standardLayoutWithin` and `emptyWithin` take
  it too. `constructible` is `false` at an abstract class, `aggregate`
  is `false` at a polymorphic one, and `Program.call` is ill-formed when
  the selected function takes an abstract class by value. Member lookup
  needs no change: an override is found as the derived class's
  declaration, which is the final overrider at that static type, and the
  dynamic type is outside the fragment. `virtualsWellFormed` checks
  `final` and `override`. Theorems: `polymorphic_not_trivial` (no
  special member of a polymorphic class is trivial, so it is neither
  trivially copyable nor standard-layout), `abstract_not_constructible`,
  `abstract_by_value_ill_formed`, `override_is_correspondence`,
  `virtual_destructor_inherited`. Emitted cases on the traits and the
  by-value call.
- **Exception specifications.** `noexcept : Option Bool` on every
  function-like declaration, `none` for no specifier, and
  `noexcept : Bool` on `Ty.fn`. `Program.throwingWithin fuel c k` is
  the implicit rule for a defaulted special member, through the
  function resolution selects for each subobject, beside `trivialWithin`
  and like it, with the facts at the fuel below and its own recursion
  for the subobjects' members; `Program.throwing` of any function is its
  specifier, the implicit rule, or potentially throwing.
  The `is_nothrow_` traits are the base trait and `!throwing` of the
  selected operation; `is_nothrow_invocable` reads the function type;
  `is_nothrow_swappable` is the move constructor and move assignment
  non-throwing when no `swap` is declared, and residue otherwise.
  `destructible` in `Concepts` becomes real. Theorems:
  `nothrow_propagates` (a potentially-throwing subobject destructor
  makes the enclosing destructor potentially-throwing),
  `implicit_noexcept_from_subobjects` (a flat class with non-throwing
  members has non-throwing special members), `override_keeps_noexcept`
  as a well-formedness check, and the restatement of
  `nothrow_destructible_eq` as a theorem about classes without a
  specifier. Emitted cases on the `is_nothrow_` traits with
  `noexcept(false)` members and the `destructible` concept.
- **Aggregates.** `Program.aggregate c` by [dcl.init.aggr]/1;
  `elements c` by /2. `Val.obj c subs` lists the elements, bases then
  members, and `Val.Equivalent` is unchanged; `uniqueValue` and
  `candidateInitializer` are restated: one value per class holds for a
  class whose elements are all classes with one value, and a converting
  constructor's result for a class with scalar members is the
  environment's oracle again, as phase 11 first planned.
  `Program.braceInit c inits` is aggregate initialization from a list
  of argument types, with `{}` for the unlisted elements and a
  reference element without an initializer a failure; for a non-aggregate
  `T{}` is value-initialization, the default constructor.
  `constructible` gains the parenthesized aggregate branch of
  [dcl.init.general]/15. `default_initializable` in `Concepts` gets its
  three conjuncts. `Trait.isAggregate`, `isImplicitLifetime`. Theorems:
  `aggregate_elements_are_value` (a class value's subobject list is the
  aggregate's element list), `brace_init_differs_from_default_init`
  (a `const` member: `T{}` well-formed, `T t;` not),
  `paren_aggregate_constructible` (`is_constructible<Agg, int>` for an
  aggregate with one `int` member, where the model said `false`),
  `aggregate_iff_declarations`. Emitted cases on `is_aggregate`,
  `is_implicit_lifetime`, `is_constructible` through the aggregate
  branch, and `default_initializable` at the `const`-member class.
- **The encoding.** Each stage adds its theorems to
  `Overload/Typeclass/ValueNature.lean`: a polymorphic instance type is
  not trivially copyable, so the value route copies it in earnest, and
  an abstract one cannot take the by-value route at all
  (`virtual_instance_costs`, `abstract_instance_by_reference`); an
  instance type with no members has non-throwing special members and
  models `destructible`, and a constraint on `is_nothrow_copy_constructible`
  of a callable is the noexcept-correct form of the callable-copying
  rule (`instance_nothrow`, `nothrow_copy_constraint`); an instance
  type is an aggregate and an implicit-lifetime class, so `X{}` in the
  value route is aggregate initialization of the empty element list
  (`instance_is_aggregate`).

### Stages

1. [virtual-functions](#virtual-functions): `Virt`, `polymorphic`,
   `abstract`, `finalOverrider`, `virtualsWellFormed`, the triviality,
   layout and emptiness conjuncts, the abstract checks in
   `constructible` and `Program.call`, the three traits, the five
   theorems, the encoding's two, emitted cases, docs and citations.
2. [exception-specifications](#exception-specifications): `noexcept` on
   declarations and `Ty.fn`, `throwingWithin` in `Facts`, `throwing`,
   the `is_nothrow_` traits, `destructible` made real, the four
   theorems, the encoding's two, emitted cases, docs and citations.
3. [aggregates](#aggregates): `aggregate`, `elements`, `Val.obj` as the
   elements with `uniqueValue` and `candidateInitializer` restated,
   `braceInit`, the parenthesized aggregate branch of `constructible`,
   `default_initializable`'s three conjuncts, `isAggregate` and
   `isImplicitLifetime`, the four theorems, the encoding's one, emitted
   cases, docs and citations.

## Phase 15: class templates and their members

Planned 25 October 2026. The fragment's class templates are `template
<head> struct name {};` with nothing inside. `Decl.classTemplate` has a
name, a head and a scope, no bases and no members, and nothing in the
model looks inside a specialization: `Program.directBases` gives
`X<int>` no bases, `Program.memberScope?` finds no scope for it, and so
`is_invocable<X<int>, A>` has no call operators to find, the trait
inherits that, and the decision log carries it as residue
(`decisions.md#trait-residue`). The residue wording was a symptom. What
is missing is members of class templates in general: declarations
stated in the head's parameters, the substitution of a specialization's
arguments into them when the specialization is looked into, and the
instantiation and point-of-instantiation rules that say when that
happens and what it produces.

That is also the shape the encoding has and the model has stood in for.
beman.transpose's derivation base is `template <class Impl> struct
derive_functor : protected Impl`, with member templates `fmap` and
`replace` constrained by requires-expressions over `Impl`
(`src/smd/overload/encoding.hpp`), and an instance is a specialization
of it. The model declares `derive_functor` as a plain class where it
needs the name (`Overload/Typeclass/Lookup.lean`,
`Overload/Typeclass/Inheritance.lean`), names an instance's value by the
type `instance_of<a, i>`, and answers the operation object's constraint,
`TC.fmap(declval<F>(), declval<T>())`, by an oracle that says true
exactly when the lookup selects an instance (`memberAtomics`,
`Overload/Typeclass/Encoding.lean`). Every theorem about the instance's
members takes that answer as a hypothesis (`Overload/Typeclass/Members.lean`),
and the accurate-members obligation rests on an audit, not a
computation. With class template members the member call is resolved
on the instance's type, the hypothesis becomes a theorem about the
computed environment, and the derivation base's accuracy is a theorem
about the reduced encoding.

The phase is the Standard side first. A class template gets bases and
members, a specialization gets the template's member declarations with
its arguments substituted, member lookup and the call on an object are
keyed by type rather than class name, and the traits and special
members follow because they are already keyed by type. The typeclass
side then declares the real derivation base and resolves the member
call. Explicit and partial specializations of class templates stay out:
the encoding's instances are partial specializations of a variable
template, which the model has had since phase 1, and the members of an
explicit or partial specialization are unrelated to the primary's
([temp.expl.spec]/6, [temp.spec.partial.member]/1), so admitting them
would be a second member mechanism for no consumer.

### The rules to transcribe, as they stand in N5054

Paragraph numbers counted from `\pnum`, as `make drift-check` does.

| Rule | N5054 text (abbreviated) | Model counterpart | Stage |
|---|---|---|---|
| [temp.class.general]/1 | A class template defines the layout and operations for an unbounded set of related types. | `Decl.classTemplate` gains `bases` and `protectedBases`; its members are declarations like a class's. | 1 |
| [basic.scope.class]/1 | Any declaration of a class or class template `C` introduces a class scope that includes its member-specification. | The class template's scope is the same `.class n` step a class's is; `Program.classScope?` finds it for a class template too. | 1 |
| [temp.dep.type]/1, [temp.decls.general]/2, [temp.local]/1 | In the definition of a primary class template or its member, the name of the class template followed by the template argument list of its template-head refers to the current instantiation; the primary's argument list is its head's; the injected-class-name used as a type-name is that spelling. | `Program.currentInstantiation n h : Ty`, `X<T0, …>` as `.spec' n (params h)`. A member, special member or conversion of a class template is declared for that type: `Decl.member (currentInstantiation n h) m`. | 1 |
| [temp.mem]/1 | A template declared within a class template is a member template; defined outside, it takes the class's template-head followed by its own. | A member template's head is its own; its declaration refers to the class's parameters as `.param i` for `i` below the class head's length and to its own as `.param (n + j)`. Instantiation substitutes the class's arguments and renumbers its own to `.param j`, one `Constraint.substArgs`/`Ty.subst` with the list `args ++ [.param 0, …]`. | 1 |
| [temp.mem.func]/2 | The template arguments for a member function of a class template are determined by the template arguments of the type of the object for which it is called. | `Program.specializationBindings? c : Option Bindings`, the explicit-argument and default steps over the head with the specialization's arguments, as `validType` runs them ([temp.names]/13). `member_template_arguments`: deduction for the instantiated member is deduction for the member with the class's arguments as leading explicit arguments. | 1 |
| [temp.res.general]/1 sentence 2 | A dependent name is looked up for each specialization, after substitution. | The substitution precedes every lookup into a specialization: `Decl.instantiate σ` on the found declarations. | 1 |
| [temp.inst]/2 | A class template specialization is implicitly instantiated when referenced in a context that requires a completely-defined object type or when its completeness affects the semantics of the program. | Looking into a specialization, for a member, a base, a special member or a trait, is such a context. The model instantiates on lookup and nowhere else. | 2 |
| [temp.inst]/3 | The implicit instantiation of a class template specialization causes the implicit instantiation of the declarations, not the definitions, of its member functions, member templates and friends. | `Program.instantiatedMembers c`: the template's member declarations with `σ` substituted. The fragment has no definitions, so this is the whole of instantiation. | 2 |
| [temp.inst]/10 | If the function selected by overload resolution can be determined without instantiating a class template definition, it is unspecified whether that instantiation takes place. | Nothing: a specialization that is only an argument type is never looked into, and no theorem rests on an instantiation happening. | 2 |
| [temp.spec.general]/2, /4 | A class instantiated from a class template is an instantiated class; a member function instantiated from the member definition is an instantiated member function; a specialization is a class or member instantiated from a templated entity or explicitly specialized. | The instantiated declarations are ordinary `Decl`s for the ground type `X<int>`, so every judgement over a class applies to them unchanged. | 2 |
| [temp.dep.type]/3, [class.member.lookup]/4 | A dependent base class is a dependent type that is not the current instantiation; the lookup set merges the direct non-dependent bases. | `Program.directBases (.spec n as)` is the template's bases with `σ` substituted, no longer dependent; the merge of /4 runs over them. `Subobject` becomes a path of types. | 2 |
| [temp.point]/4 | The point of instantiation of a class template specialization referenced from a non-template context immediately precedes the namespace-scope declaration that refers to it. | `Program.pointOfInstantiation c : Option Nat`, the position of the first declaration that mentions `c`. | 2 |
| [temp.point]/7 sentence 3 | A specialization for a class template has at most one point of instantiation within a translation unit. | `specialization_members_fixed`: the member search of a specialization gives the same declarations from every point at or after its point of instantiation, under `Program.templatesWellFormed`, the program-shape check that a class template's members precede the first declaration that refers to a specialization of it. | 2 |
| [over.call.object]/1 to /3, [func.require]/1, [meta.rel]/3 | The call on an object of class type; `INVOKE`; `is_invocable`. | `classCallee : Ty → Option Ty`, `objectCandidates`, `impliedObject`, `objectCallAt` keyed by type; `specialization_callee_invocable` closes the residue. | 2 |
| [over.match.funcs.general]/2 to /4 | The implicit object parameter and the implied object argument of a member call. | `Program.memberCallAt` leads its argument list with the implied object argument, as the object call does since 25 October 2026; the member functions being `const`, no earlier case moves. | 2 |
| [class.copy.assign]/7, [class.default.ctor]/2 | A reference member deletes the defaulted copy and move assignment; a reference member without an initializer deletes the default constructor. | `argument_reference_deletes`: a class template with a member of its parameter's type has these deleted at a reference argument and not at an object type, by `value_nature_iff` over the instantiated members. | 2 |
| [temp.deduct.general]/5, [temp.constr.decl], [expr.prim.req.compound]/1 | The operation object's constraint is a requires-expression whose expression is a member call. | `Env.fullWithin` answers the atom `fmap_call` by resolving `TC.fmap(declval<F>(), declval<T>())` on the instance's value type with the lookup's object as the implied object argument (`Program.memberInvoke`). `Decl.instance` gains the value's type; `Env.instantiate` returns it. `operation_constraint_is_member_call`. | 3 |
| [class.member.lookup]/3 | The declaration set is the class's own when not empty. | `derivation_base_accurate`, and the hidden-member example on the real shape: an instance type deriving from `derive_functor<I>` that declares its own `fmap` hides the constrained one. | 3 |

Out of the fragment, stated in the decision: explicit specializations
of class templates and their members ([temp.expl.spec]/6), partial
specializations of class templates and their members
([temp.spec.partial.member]/1), member definitions outside the class
([temp.mem.func]/1, [temp.mem.class], [temp.static]), static data
members, member classes, friends, member enumerations, dependent names
inside a template's own definition (every use of the fragment is
outside every class, so lookup into the current instantiation never
runs), the incomplete type of a declared-but-undefined template
([temp.inst]/2 sentence 3), and the multiple points of instantiation of
a member function specialization ([temp.point]/7 sentences 1 and 2),
which concern definitions.

### Design

- **Members of a class template.** A member, a special member and a
  conversion of a class template are `Decl.member`, `Decl.special` and
  `Decl.converting` for the current instantiation, `currentInstantiation
  n h = .spec' n [.param 0, …]`, exactly the spelling the Standard uses
  for an out-of-line member, `A<T1,T2>::f1`. A member function or member
  function template is a `Decl.function` or `Decl.functionTemplate`
  whose scope ends in `.class n`, as a class's does, with the class's
  parameters as `.param i`. `Decl.classTemplate` gains `bases` and
  `protectedBases`, which may be dependent: `derive_functor : protected
  Impl` is `protectedBases := [.param 0]`. The flat program stands, and
  `Decl.isMember` is unchanged.
- **Member templates.** A member template's own head follows the
  class's in the numbering: with a class head of length `n`, the
  member's `j`th own parameter is `.param (n + j)` in its declaration.
  `Program.specializationBindings? (.spec n as)` runs `explicitStep` and
  `defaultsStep` over the class head, as `validType` does, and
  `Decl.instantiate` substitutes with the argument list `as' ++ [.param
  0, …, .param (own - 1)]` through `Constraint.substArgs` and `Ty.subst`,
  which are single-pass, so the class's arguments go in and the
  member's own parameters come out renumbered from zero in one
  substitution. The emitter names a parameter by its index, so the
  class's are `T0, …` and the member's own continue the count, which is
  what C++ needs for the two heads. A ground class has `σ = []` and
  `Decl.instantiate` is the identity on it (`instantiate_ground`), so
  the ground and template cases are one code path.
- **Instantiation on lookup.** `Program.classKey? : Ty → Option (Ty ×
  Bindings)`: a class name is itself with no bindings; a specialization
  of a declared class template with a valid argument list is the
  current instantiation with the bindings; anything else is none.
  `membersOf`, `specialDecls`, `conversionsOf`, `directBases` and
  `declarationSet` look the key up and instantiate what they find. The
  lookup set over bases, `lookupSetWithin`, recurses through
  `directBases`, which are substituted first, so the merge of
  [class.member.lookup]/4 sees no dependent base. `Subobject` becomes
  `List Ty`. Every function of `Overload/Members.lean` that took a class
  name takes a type: `memberSearch`, `callOperators`, `surrogates`,
  `objectCandidates`, `impliedObject`, `objectCallAt`, `memberCallAt`,
  and `classCallee` in `Overload/Requires.lean` returns the type.
  `Program.trait` and `Program.special` are already keyed by type and
  need no change beyond the primitives beneath them.
- **The member call's object.** `memberCallAt` leads with
  `impliedObject cls`, the const lvalue the object call uses, and the
  found members carry their implicit object parameter through
  `Decl.withImplicitObject`. The fragment's member functions are all
  `const`, so the object binds by the identity and no earlier resolution
  changes; `member_call_object_inert` says so for the concrete programs
  that exist, and the general inertness theorem the surrogate stage owes
  is stated for both calls at once.
- **Point of instantiation.** `Program.pointOfInstantiation c` is the
  position of the first declaration that mentions `c`, where
  [temp.point]/4 puts the point for a specialization referenced from a
  non-template context. `Program.templatesWellFormed`: every member of a
  class template follows its declaration and precedes that point, for
  every specialization the program mentions. Under it, the member search
  of a specialization is the same from every position at or after the
  point (`specialization_members_fixed`), which is what "at most one
  point of instantiation" means for a model without definitions. The
  dependent-call machinery of phase 9 is untouched: a member call on a
  specialization is not a dependent call, since its callee is not an
  unqualified-id.
- **The typeclass side.** `Decl.instance` gains `value : Option Ty`, the
  type of the instance's value, mentioning the pattern's parameters;
  `Env.ofProgram`'s `instantiate` returns it with the pattern's deduced
  bindings substituted, and `instance_of<a, i>` stays the name when none
  is given, so every existing theorem about lookup is unchanged.
  `derive_functor` is declared as the class template it is, with `fmap`
  and `replace` as member templates constrained by the requires-expressions
  of the header, over the member-call requirement on `const Impl&`.
  `Env.fullWithin` answers `fmap_call` one level down, as it answers a
  requires-expression and a class-callee trait: the member call
  `TC.fmap(declval<F>(), declval<T>())` on the value type with the
  lookup's object as implied object argument (`Program.memberInvoke`).
  `memberAtomics` is retired, and `ofProgram_member` is restated: the
  computed environment is the accurate member exactly when the value
  type's `fmap` is accurate, and `derivation_base_accurate` shows the
  reduced header's is. The hidden-member program of
  `Overload/Typeclass/Lookup.lean` is restated on the real shape.
- **Emitter.** A class template renders with its bases, data members,
  special members, conversions and member functions, the last with
  their own heads, as a class does; the `head` renderer takes an offset
  for a member template's own parameters. An instance with a value type
  renders `inline constexpr value tc<pattern>{}`; the emitted encoding
  cases that test which instance was selected through `selected<k>` are
  restated to test the value type.

### Decisions to record (`docs/decisions.md`)

- `class-template-members` (new): the representation above, what is
  instantiated and when, and the exclusions.
- `lookup-scope`: log entry, a class template's scope is a class scope.
- `expression-depth`: log entry, the operation object's member call
  leaves the oracle.
- `trait-residue`: log entry when stage 2 lands, closing the
  class-callee residue.
- `instance-inheritance`: log entry when stage 3 lands, the derivation
  base is real and leak 2's program is stated on it.

### Stages

1. [record-phase-fifteen](#record-phase-fifteen), docs only: this
   section, the phase row, the status, the theorem rows, the decision
   entries, `Overload.Std.inScope`, the residue notes reworded to say
   what they mean.
2. [template-members](#template-members): `Decl.classTemplate` with
   bases, `currentInstantiation`, members and member templates of a
   class template, `specializationBindings?`, `classKey?`,
   `Decl.instantiate` with `instantiate_ground`,
   `member_template_arguments`, `membersOf`, `specialDecls`,
   `conversionsOf` and `directBases` over a specialization, the emitter's
   class template body, guards.
3. [specialization-lookup](#specialization-lookup): `Overload/Members.lean`
   keyed by type with `Subobject` as a path of types, `declarationSet`
   instantiating, `classCallee` returning a type, `memberCallAt` with
   its implied object argument, `pointOfInstantiation`,
   `templatesWellFormed`, `specialization_members_fixed`,
   `specialization_callee_invocable`, `argument_reference_deletes`;
   emitted cases: a member call and an object call on a specialization,
   `is_invocable` of a specialization callee through a call operator and
   through a surrogate, traits of specializations with a member of the
   parameter's type at an object type and at a reference type, a
   specialization with a dependent base; the trait-residue log closed.
4. [derivation-base](#derivation-base): `Decl.instance` with a value
   type, `Env.instantiate` returning it, `derive_functor` as a class
   template in `Overload/Typeclass/Encoding.lean`, `fmap_call` answered
   by `Env.fullWithin` through `Program.memberInvoke`, `memberAtomics`
   retired, `operation_constraint_is_member_call`,
   `derivation_base_accurate`, the hidden-member program restated,
   emitted encoding cases on the real derivation base.
5. [class-template-docs](#class-template-docs): the guide, the
   obligations' accurate-members row, the findings, this status,
   `citations.md`, `make drift-check-current`.

### Risks, recorded so the stages can watch for them

`Decl.classTemplate` gains two fields, so every match on it is touched;
`Subobject` as `List Ty` touches `LookupSet.merge` and its agreement
proof; `classCallee` returning a type restates `invocable_class_iff_call`
and `full_invocable_class`. The `decide` proofs over `Program.call` now
run `explicitStep` and `defaultsStep` for every specialization looked
into. `inheritance_erasure` erases the bases of named classes; a class
template's dependent base is out of its reach, and the typeclass
theorems that use erasure are on concrete programs with named classes,
so none moves, but the theorem is not extended to specializations in
this phase. `Ty.subst` leaves a constant argument's parameter alone
when the binding is not a type, so a class template with a constant
parameter whose members mention it needs the `.value` case checked in
stage 1.

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
