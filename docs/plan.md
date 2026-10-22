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

Eleven phases, each closed by a theorem or a passing test set. The
typeclass results first become reachable at phase 4, before any of
call-site overload resolution exists. Phase 9 was added on 20 October
2026, after the others closed, and phase 10 on 21 October 2026.

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
  comes first. The one in-scope paragraph of the phase without a
  counterpart is [temp.point]/1, the point of instantiation after the
  declaration that refers to a specialization, which the fragment reads
  through the end-of-unit point of /7 (`citations.md`). The emitted
  cases of the phase number twenty-two and every one agrees with GCC 15
  and Clang 24; `make drift-check-current` reports one cited paragraph
  that differs on the draft's main, an editorial change
  (`decisions.md#draft-pin`).
- Phase 10 is open, 21 October 2026. Planned the same day. The plan,
  the cross-reference against N5054 and the stages are
  [below](#phase-10-template-arguments-and-their-conversion). The
  in-scope paragraphs are in `Overload.Std.inScope`, so `citations.md`
  lists them as uncovered until each stage lands.

## Target theorems

Twenty-seven theorems carry the results. A theorem that fails is recorded with
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
| [over.call.object]/1 | For a call on an object of class type the candidates include the function call operators of its class, a search for `operator()` in its scope. | None. | `objectCallCandidates`. |
| [class.member.lookup]/3 to /6 | The declaration set of a name in a class is a single search in its scope; if non-empty, done; otherwise the lookup sets of the direct bases are merged, with the hiding and ambiguity rules; an invalid set is ill-formed. | CWG2582, CWG2642. | `lookupSet`, `memberSearch`. |
| [temp.dep.general]/2 | A dependent call is an unqualified-id called with a type-dependent argument; its name is looked up at the point of instantiation in both the definition and the instantiation contexts. | None. | `Decl.dependentCall`. |
| [temp.res.general]/1 | A name in a template is looked up from where it appears. | Editorial. | The definition context. |
| [temp.point]/1, /7 | The point of instantiation of a function template specialization follows the namespace-scope declaration that refers to it; the end of the unit is another. | As above. | The instantiation context. |
| [module.context]/5, /7 | During instantiation the instantiation context holds the point of instantiation; otherwise a point's context is itself. | None. | With the above. |
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
