# Decision log

Each section answers one question, identified by a slug named for the
question, never for the chosen answer, so the slug survives a reversal. The
`assumed` attribute in the Lean sources names these slugs, and the citation
index (`citations.md`) links each assumption back here.

Entry shape: Question / Status / Decision / Why / Log.

---

## draft-pin

**Question:** Which text does the model cite?
**Status:** DECIDED 13 October 2026; tag chosen 15 October 2026.
**Decision:** The final C++26 text. Pinned to tag `n5054` of the
cplusplus/draft repository, commit `45b03900ecb77e8964ba0c8e5ae1063387c2b7de`
(working draft N5054, 16 July 2026). A drift check compares each cited
sentence with the current working draft and flags any citation that now
points at different text.
**Why:** Stable names survive renumbering between drafts; a pin makes a
citation a fact and not a moving target. N5054 is the first working
draft after the C++26 text was settled and is the tag the probe checks were
read against.
**Log:**

- 2026-10-13 — Decided on the final C++26 text.
- 2026-10-15 — Pinned to `n5054`. Whether N5054 is byte-for-byte the C++26
  DIS, or the first post-DIS working draft with editorial changes, is to be
  confirmed against the editors' report N5055; the drift check will show
  which cited paragraphs differ if the pin moves to the DIS tag.
- 2026-10-20 — `make drift-check-current` against the draft's main at
  `47974a2`: one cited paragraph differs, [temp.spec.partial.general]/7,
  cited by `reachable`. The change is markup in the example's comment,
  "using-declaration" set as a grammar term; the sentence the model
  transcribes is unchanged. No citation moves.

- 2026-10-21 — `make drift-check-current` on main at `47974a2`:
  [basic.fundamental]/1 differs from the pin only by a note, "plain
  `int`s are intended to have the natural width suggested by the
  architecture", removed on main; the normative sentences `representable`
  cites are unchanged. [temp.spec.partial.general]/7 as before.- 2026-10-24 — Phase 12 closed. `make drift-check-current` now reports
  five cited paragraphs that differ on main, the three new ones
  editorial: [class.dtor]/7, [special]/7 and [dcl.init.ref]/5
  (`findings.md`).

---

## spec-style

**Question:** Is each mechanism a relation, a function, or both?
**Status:** DECIDED 13 October 2026, provisionally.
**Decision:** Both, with an agreement theorem. Decided on the plan's
reasoning, not on experience with the cost, so phase 1 reports what the
agreement proof for deduction cost, and the question reopens if that is out
of proportion.
**Why:** The relation transcribes the Standard one sentence per constructor;
the function is what runs under `#eval` and drives the emitter. The
agreement theorem is what makes the executable side evidence about the
transcription.
**Log:**

- 2026-10-13 — Decided.
- 2026-10-15 — Phase 1 cost report. `DeduceTy` has 11 constructors and
  `deduceTy` 12 equations. The agreement theorem (`deduceTy_sound`,
  `deduceTy_complete`) is 70 lines of tactic proof, the extension lemma
  another 55, each a routine structural induction with one `cases` per form.
  The cost is in proportion. What made it routine was keeping `Ty` one
  inductive type (argument lists are `nil`/`cons` constructors of `Ty`)
  instead of a nested or mutual definition; see the module docstring of
  `Overload/Syntax.lean`.
- 2026-10-16 — Deviation, to repair: partial ordering
  (`Overload/Ordering.lean`) and overload resolution
  (`Overload/Resolution.lean`) are given in the executable form only.
  Their relation forms, and the agreement theorems, are owed; matching
  has both (`PatternMatches`, `patternMatches_iff`). The executable
  forms carry the citations meanwhile, one per sentence, so the index is
  complete.
- 2026-10-16 — Partial specialization selection now has both forms:
  `Selects`, one constructor per case of [temp.spec.partial.match]/1, and
  `select_iff`. The relation is stated over the executable
  more-specialized, since ordering still has no relation form. The
  agreement proof is about 160 lines, most of it list bookkeeping for
  positions. Coherence and stability are proved from the relation, not
  from the function, which is the payoff the decision expected.
- 2026-10-17 — The deviation is repaired. `Overload/Specs.lean` gives
  partial ordering and overload resolution their relation forms, each
  constructor cited, with agreement theorems: `DeducePairs`,
  `AtLeastAsSpecialized`, `MoreSpecialized`, `BetterFunction`,
  `BestViable` and `Resolves`. The relations are built on `DeduceTy` and
  on each other. At the leaves they use the executable parts that are
  definitions rather than rules: the transformed template, the nominated
  types, the /9 denial, the gate, more-constrained and the ranking. The
  file is about 350 lines, most of it the agreement proofs. `Selects`
  is still stated over the executable more-specialized, which
  `moreSpecialized_iff` now makes interchangeable with the relation.

---

## library-dependency

**Question:** Does the development depend on Mathlib?
**Status:** DECIDED 13 October 2026.
**Decision:** Lean core plus Batteries, without Mathlib.
**Why:** The order theory needed is small enough to state by hand, and the
development stays readable to a C++ audience and to its author.
**Log:**

- 2026-10-13 — Decided.
- 2026-10-15 — Batteries pinned at `v4.35.0` with Lean `v4.35.0`
  (see [toolchain-pin](#toolchain-pin)). Nothing from Batteries is used
  yet; the dependency is in place for the order theory of phases 3 and 4.

---

## expression-depth

**Question:** How much of the expression language is modelled?
**Status:** DECIDED 13 October 2026.
**Decision:** None for now, with validity as a pure oracle. That suits the
check of whether an object has the shape of a typeclass at all. Reopen if a
proof needs to see inside a call that a constraint depends on.
**Log:**

- 2026-10-13 — Decided.
- 2026-10-16 — The oracle is `Overload.Env`, tagged with this entry: what
  a variable template specialization instantiates to, whether an atomic
  constraint holds, and whether an argument converts to a non-dependent
  parameter type. `Env.ofProgram` derives one from a program's lookup
  declarations for the emitted cases; the draft's examples are reproduced
  with hand-written oracles in `OverloadTest/Steps.lean`.
- 2026-10-21 — Phase 10 adds one oracle, `Env.subobject`: the base
  subobject of a class value, for a derived value supplied to a
  base-typed constant parameter. `Env.ofProgram` computes it from the
  program's class declarations, as it computes `bases`.
- 2026-10-23 — Phase 11 planned a second oracle for the value a
  converting constructor gives a class-typed constant parameter, since a
  constructor body is an expression. It turned out not to need one: the
  oracle is `Env.initializer`, the former `subobject` renamed for what it
  now answers, the candidate initializer of [temp.arg.nontype]/3, and
  `Env.ofProgram` computes it as `Program.candidateInitializer`, whose
  user-defined case is the class's one value in the fragment
  (`findings.md`). Conversion functions and constructors are declarations
  by type (`user-defined-conversions`), still no expressions.
- 2026-10-24 — Phase 12 shrinks the oracle. The type traits and
  requires-expressions the fragment can state become judgements:
  `Constraint.trait` is answered by `Program.trait` from the types, the
  special member functions and the calls the model decides, and a
  requirement's expression is a call decided by `callAt`. The string
  atom and the oracle stay for the residue (`trait-residue`). Still no
  expressions: a default member initializer is a flag, a requirement is
  a call by callee and argument types.
- 2026-10-24 — Stage 5 of phase 12 landed. A requires-expression is an
  atom the environment answers; the base environment, `Env.ofProgram`,
  cannot resolve its calls, which need the lookup above it, so
  `Env.full` answers them one level deep (`Overload/Requires.lean`). The
  oracle's atoms are now expressions, traits, requires-expressions and
  unexpanded concept-ids.

---
- 2026-10-25 — Phase 15 planned: the operation object's constraint,
  the member call `TC.fmap(declval<F>(), declval<T>())`, is to leave the
  oracle (`memberAtomics` on the typeclass side) and be resolved on the
  instance's value type by `Env.fullWithin`, as a requires-expression
  and a class-callee trait are.
- 2026-10-26 — Landed as `fmapResolved` and
  `operation_constraint_is_member_call`: the member call is resolved on
  the type the instance declares its value to have. The oracle stays
  for the abstract object, as its specification; `inaccurate_oracle_example`
  is an argument list where the two differ.

## lookup-scope

**Question:** Is name lookup, including argument-dependent lookup, in the
model?
**Status:** DECIDED 13 October 2026; reversed 20 October 2026.
**Decision:** Yes, for a fragment: namespace scopes and class scopes,
unqualified lookup, argument-dependent lookup, member lookup, and the
lookup of a dependent call in its two contexts, as P1787R6 wrote them and
as they stand in N5054. Out of the fragment, and stated as such:
using-directives and using-declarations, inline and unnamed namespaces,
block scopes, modules and reachability by import, friends, splices,
parenthesized callees, conversion-function-ids, explicit object
parameters. A call's candidate set is computed from a program point and
a scope; the existing resolution theorems keep their candidate-list
parameter and the new theorems compose lookup with them.
**Why:** The claims the obligations rest on are lookup claims: a variable
cannot be overloaded, argument-dependent lookup adds nothing when ordinary
lookup finds an object, member lookup stops at the first class that
declares the name, the lookup variable is one entity in every unit. They
were prose. P1787R6 gives each a single-search formulation that fits the
relation-plus-function style, so they can be theorems. The plan's phase 9
section has the cross-reference and the stages.
**Decided by:** the author, on the plan of 20 October 2026.
**Log:**

- 2026-10-13 — Decided: no. Whatever is found outside the model is not
  part of the model. A customization point object such as `fmap` that
  dispatches to an instance is in the model, as a fixed candidate set. A
  member such as a hypothetical `std::vector::fmap`, or a delegation to
  `ranges::transform`, is outside it and enters only as an opaque
  candidate.
- 2026-10-15 — `Program.candidates` is the candidate set: the declarations
  with the callee's name, in order.
- 2026-10-20 — Reversed, as above. `Program.candidates` stays as the
  input of every existing theorem; a redeclaration in it is today two
  candidates and a spurious ambiguity, which phase 9's first stage
  repairs. The syntax is [scope-syntax](#scope-syntax).
- 2026-10-20 — Landed through member lookup: `Overload/Scope.lean`,
  `Names.lean`, `Adl.lean`, `Members.lean`. A call from a point
  (`Program.callAt`) finds its candidates by unqualified lookup,
  argument-dependent lookup when it applies, and for an object the call
  operators of its class. The member call at the operation object's
  constraint stays the oracle of [expression-depth](#expression-depth),
  since a constraint's probe is an expression; `Program.memberCallAt`
  computes a member call on the fragment's members.

---
- 2026-10-25 — Phase 15 planned: a class template's scope is a class
  scope ([basic.scope.class]/1), the same `.class n` step a class's
  members use, and a specialization's members are what that scope
  declares with the specialization's arguments substituted.

## ranking-fidelity

**Question:** Is implicit conversion ranking a parameter or a modelled
mechanism?
**Status:** DECIDED 13 October 2026. Confirmed 17 October 2026 by the
separability theorem.
**Decision:** A parameter for the core theorems. Dispatch is user-written,
so constraint exclusion, `if constexpr` chains and priority tags will all
occur. One concrete ranking, covering priority tags and reference binding,
is supplied so the model can say which styles are safe.
**Log:**

- 2026-10-13 — Decided.
- 2026-10-17 — The concrete ranking is `Program.ranking` in
  `Overload/Ranking.lean`: identity and derived-to-base conversions,
  direct reference binding, and the tiers of [over.ics.rank]/3. The
  emitted call cases are computed with it, and every compiler agrees on
  the eleven cases that exercise it. Separability holds for any two
  rankings, with no hypothesis on either (`separability`), so the
  parameter costs the core theorems nothing. `identityRanking` stays for
  the unit tests.

---

## missing-instance

**Question:** Is a missing instance a soft failure or a hard error?
**Status:** DECIDED 13 October 2026.
**Decision:** Soft, by construction. The default instance is
`std::false_type`, so lookup always succeeds and absence is checkable. The
stability theorem and the step-order lemma still have to confirm that
nothing else on the path fails hard.
**Why:** Probe variant D compiles and selects correctly on both compilers
(`probes.md`).
**Log:**

- 2026-10-13 — Decided.
- 2026-10-15 — The encoding in `src/smd/overload/encoding.hpp` spells it:
  the primary `functor<T>` is `std::false_type`, and the operation object is
  constrained on `has_instance_v`.
- 2026-10-16 — Corrected to match beman.transpose: the operation object
  is constrained on the call through the instance, `requires { TC.fmap(...)
  }`, not on `has_instance_v`, and `derive_functor` inherits `Impl`
  protected. Soft failure still holds by construction, because
  `std::false_type` has no `fmap`.
- 2026-10-16 — Confirmed by theorem: `fmapObject_outcome` shows that a
  missing instance makes the operation object's deduction fail softly,
  and only an ambiguous lookup fails hard.

---

## instance-inheritance

**Question:** May instance types for related typeclasses be related by
inheritance?
**Status:** DECIDED 17 October 2026.
**Decision:** Allowed. Inheritance between instance types is a choice an
implementer can make, and the model treats it as one. The work is to find
the problems it causes and say, for each, whether it is a matter of
education, an obligation on someone, or a bug to fix.
**Why:** The point of the work is to state what a typeclass implementer
owes. Forbidding inheritance would only be worth it if it were harmful, and
it would then need a technical means of enforcement, which is unlikely to
exist. So it is allowed, and its consequences are harvested as obligations
(`obligations.md`): exact-type use, and superclass coherence.
**Decided by:** the author.
**Facts recorded 13 October 2026:** The relation varies by kind and may vary
within a kind, since not every Functor is an Applicative and a type may
admit more than one instance. Where a relation exists it runs from the
stronger class to the weaker. A Monad instance offers `as_functor`, which
returns `derive_functor<M>`, a fresh type that supplies the Functor
operations from the Monad ones.
**Log:**

- 2026-10-13 — Opened.
- 2026-10-15 — Leak 4 (constant-parameter conversion) is live under C++26
  per the probe verdicts: a derived instance supplied as a literal template
  argument for a base-typed constant parameter is sliced and identified with
  the base value. The exact-type obligation now covers constant parameters
  as well as function parameters.
- 2026-10-17 — Evidence for an answer, not a ruling. Inheritance erasure
  is proved for the model's fragment (`inheritance_erasure`). Erasing the
  base classes of a set of instance types changes no call that uses every
  class erasure touches at its exact type. Outside that fragment erasure
  changes outcomes (`erasure_needs_exact_type`, `rank_beats_refinement`).
  Superclass coherence is a law, since a retrieved Functor and the
  canonical one are different template arguments (`superclass_identity`).
  The proposed answer is the plan's guidance: inherit if you like, but
  never name an instance type in a signature, and keep a retrieved
  superclass instance law-compatible with the canonical one. Two gaps
  remain before it can be settled. Deduction from a derived class (leak
  2) is not modelled, and neither is access to the protected base that
  `derive_functor` uses. Update the same day: leak 2 is now modelled and
  is a theorem (`derived_class_deduction`), and erasure asks that no
  argument of a touched class be deduced from as a derived class. Access
  to a protected base is the gap that remains. beman.transpose relates no two instance types
  by public inheritance: `derive_monad` grows only the Functor basis, and
  `as_functor` returns `derive_functor<M>`, which has `M` as a protected
  base.
- 2026-10-17 — Decided by the author: allowed. The known problems are leak
  1 (rank beats refinement), leak 2 (deduction from a derived class), leak
  3 (two paths to the superclass) and leak 4 (constant-parameter slicing),
  all recorded as obligations. Access to a protected base is still
  unmodelled, and is the next place to look for a problem.
- 2026-10-17 — Access is modelled (`Overload/Access.lean`). A protected
  base, as `derive_functor` has, does not hide the implementation from
  overload resolution: ranking ignores access, deduction from a derived
  class goes through the base, and a selected conversion to it makes the
  call ill-formed (`protected_base_selected_ill_formed`,
  `protected_base_deduced_ill_formed`). It is the exact-type obligation
  again, with the implementation's types among those a signature must not
  name.
- 2026-10-21 — Phase 10 makes leak 4 a theorem: a derived value supplied
  for a base-typed value parameter is sliced to the base subobject, and
  the two name one specialization (`slicing_identifies`). A reference
  parameter denotes the object, so the library's `const auto&` parameters
  are what closes the leak (`reference_keeps_identity`).
- 2026-10-23 — Leak 5, conversion between instance types, is planned as
  phase 11 (`plan.md`). It is the leak the encoding avoids by design:
  refinement is a concept on the shape and a retrieval function, never
  a converting constructor, and the phase's theorems say what a
  converting constructor would cost.
- 2026-10-23 — Leak 5 is theorems (`Overload/Typeclass/Conversion.lean`):
  a conversion fires at no deduced parameter
  (`conversion_invisible_to_deduction`), loses by rank where a signature
  names an instance type (`conversion_loses_rank`), makes two such
  signatures ambiguous (`converting_sites_ambiguous`), yields a
  temporary the pinning routes refuse and the value route identifies
  (`converted_instance_temporary`, `value_route_identifies_converted`),
  and does nothing at all when explicit (`explicit_conversion_dead`).
  The obligation is refinement by shape (`obligations.md`).

---
- 2026-10-26 — Phase 15's derivation-base stage declares
  `derive_functor<Impl>` as the class template it is, with its
  constrained member templates and its protected dependent base
  (`Overload/Typeclass/Derivation.lean`). Leak 2's program is unchanged:
  deduction from a derived class reads the base's name and arguments,
  never its members, so `derived_class_deduction` stands as stated.

## termination-condition

**Question:** Which restriction on instance requirements guarantees lookup
terminates?
**Status:** DECIDED 13 October 2026.
**Decision:** Structural decrease on the type being served. No current
instance depends on a larger type and there is no reason to support one.
Exhausting instantiation depth is treated as a mistake by the author, not a
case the model admits, so there is no fuel and no depth outcome.
**Log:**

- 2026-10-13 — Decided.

---

## single-tu

**Question:** When does the model admit more than one translation unit and
points of instantiation?
**Status:** DECIDED 13 October 2026.
**Decision:** After phase 6, as phase 8. Different units making different
choices is expected, and is ill-formed with no diagnostic required for a
reason. Phase 8 tests the conjecture that such divergence lands in
different resolved functions, not in one function with two meanings.
**Why:** The standing assumption hides the real coherence hazards of C++.
It is written down as a tagged predicate so a later phase can remove it.
**Log:**

- 2026-10-13 — Decided.
- 2026-10-15 — `Overload.SingleTranslationUnit` carries the tag; it is the
  predicate `Program.declaredBeforeUse`.
- 2026-10-17 — How phase 8 models what cannot be said, decided by the
  author. The model does not give a meaning to a program with two
  contrary definitions of one entity. A program becomes a list of
  translation units, each resolved on its own as now. The fourth outcome
  is a verdict about the program, not a substitution outcome: ill-formed,
  no diagnostic required, naming the rule and the use, and nothing more.
  divergence-separation compares what two units resolve. Where the
  instance is a template argument, the units have different
  specializations, which is fine. Where it is looked up inside the
  function, they name one specialization with two meanings, and the
  verdict cites the rule. "Whereof one cannot speak, thereof one must be
  silent."
- 2026-10-17 — `Program.declaredBeforeUse` is restated: no instance of a
  typeclass is declared at or after a use of its lookup. It no longer
  depends on the lookup being declared. For one unit it is what keeps
  every use free of a verdict (`verdicts_single`).
- 2026-10-20 — Phase 9 adds a fourth verdict, for a dependent call whose
  definition and instantiation contexts miss a better-matching overload
  in an associated namespace ([temp.dep.candidate]/1), and a fifth for
  one entity with two definitions ([basic.def.odr]/16), which
  `operation_object_not_separated` reports in prose today. `reachable`
  is to cite [temp.spec.partial.general]/7, the sentence it transcribes.
- 2026-10-20 — The fourth verdict is in (`IllFormedNdr.dependentCandidate`,
  `Units.dependentVerdicts`, `Units.allVerdicts`). The instantiation
  context of a dependent call is the end of its unit, as `laterInUnit`
  already takes it, and the units compared are the program's.
- 2026-10-20 — The fifth verdict is in (`IllFormedNdr.odrMismatch`,
  `Units.odrVerdicts`), and `odr_verdict_implies_verdict` shows it is
  never the first: the verdicts of phase 8 already cover a lookup two
  units instantiate differently.
- 2026-10-22 — A sixth verdict, for [temp.point]/1: a dependent call's
  specialization has a point of instantiation after each namespace-scope
  declaration that refers to it (`Decl.refersTo`) and one at the unit's
  end (`Program.instantiationPoints`); its lookup runs from the first
  point ([module.context]/5), and a call that resolves differently at
  two of its points is `IllFormedNdr.laterCandidate` ([temp.point]/7).
  A program with no referring declaration has the one point it always
  had (`pointVerdict_unreferenced`). GCC and Clang fix the meaning at
  the first point too, which is one of the readings the verdict allows.

---

## test-oracle

**Question:** Which compilers are the oracle, and how is a disagreement
recorded?
**Status:** DECIDED 13 October 2026.
**Decision:** The suite runs locally, so the primary oracle is current GCC
and Clang. MSVC and EDG are consulted through Compiler Explorer for the
hand-written probes and for any case where the two primaries disagree. A
disagreement is filed as a finding against the cited sentence, never
resolved by majority, and a failure to build an in-scope example counts as
a disagreement.
**Log:**

- 2026-10-13 — Decided.
- 2026-10-15 — `scripts/differential.sh` compiles every emitted program with
  each compiler and fails on a disagreement unless it is listed in
  `differential/known-disagreements.txt`; findings go in `findings.md`.

---

## citation-granularity

**Question:** Does a citation name a paragraph or a sentence?
**Status:** DECIDED 13 October 2026.
**Decision:** The sentence, using the draft's own sentence anchors, with the
draft commit recorded once for the whole development.
**Log:**

- 2026-10-13 — Decided.
- 2026-10-15 — The attribute accepts `stable.name#para` as well as
  `stable.name#para.sentence-n`; a paragraph-level citation is for a rule
  that transcribes a list the paragraph holds as a whole, such as the
  bullets of [temp.type]/2.
- 2026-10-23 — The attribute takes several citations in one role,
  `@[std rule "a" "b"]`. A parametric attribute keeps one parameter per
  declaration, and two `std` attributes in one list had kept only the
  last (`findings.md`).

---

## p3606-mode

**Question:** Does the model transcribe the C++26 text, under which
deduction runs for every template candidate, or the P3606 rule, under which
a perfect non-template match suppresses it?
**Status:** DECIDED 21 October 2026, as to the model. The question of
what the Standard will say stays open at WG21.
**Decision:** Both. The model keeps the P3606 rule as the `.p3606` mode of
`Overload.Mode` beside the text's `.text`, which stays the default, and
the theorems that say where the two differ stay. Neither mode is
removed while the proposal's wording is unsettled.
**Why:** The question is open in the committee, not here, and the two
readings are interesting exactly where they differ: the step-order
hazard, the [temp.constr.atomic]/3 example, and the two widths of the
shortcut that GCC and Clang ship. A model that carried one reading would
lose the comparison that made those findings.
**Decided by:** the author.
**Log:**

- 2026-10-13 — Opened.
- 2026-10-16 — The two emitted step-order cases are the first entries in
  `differential/known-disagreements.txt`, for GCC. The switch is not yet
  in the model; `deduceTemplate` transcribes the text.
- 2026-10-16 — The switch exists: `Overload.Mode`, `.text` or `.p3606`,
  on `generate` and `resolve` in `Overload/Resolution.lean`. Under
  `.p3606` a non-template candidate that is a perfect match suppresses
  deduction for every template candidate. "Perfect match" is the model's
  reading of a proposal whose wording is not settled, so `perfectParam`
  carries this entry's tag: the parameter type is the argument's own type,
  with its value category for a reference parameter, and no default
  argument is used. The theorems `generate_agree_of_no_perfect`,
  `generate_p3606_suppresses` and `generate_differ_implies_perfect` say
  the modes differ exactly when a perfect match exists, and then only in
  that templates are never deduced. GCC 13 compiles the two emitted
  hazard cases, as the P3606 mode predicts, but rejects the draft's
  [temp.constr.atomic]/3 example, which the P3606 mode also predicts
  well-formed: GCC's shortcut is narrower than the rule as read here
  (`findings.md`). Default stays `.text`.
- 2026-10-16 — Clang 21 to 24 compile all three cases, the
  [temp.constr.atomic]/3 example included, so Clang's shortcut is the
  rule exactly as `.p3606` reads it, and GCC's is narrower. Clang 18 to
  20 follow the text. The question of what "perfect match" suppresses
  now has two shipping answers (`findings.md`). Default stays `.text`.
- 2026-10-20 — Once phase 9 computes the candidate set, the perfect match
  of `.p3606` ranges over the declarations lookup found, which for a call
  of an object are its non-template call operators. That is the reading
  of "candidate" the proposal uses; nothing in the mode changes.
- 2026-10-21 — Decided by the author: the switch stays, with both modes,
  because the proposal is still open and the difference is what is
  interesting. Which mode the Standard ends up with is logged here when
  P3606 or its successor is adopted or rejected.

---

## repository

**Question:** Name, host, licence and REUSE adoption for the development.
**Status:** DECIDED 15 October 2026.
**Decision:** `overload`, at github.com/steve-downey/overload, generated from
the steve-downey/example Copier template so that the C++ side keeps the
same Makefile, CMake, pre-commit and CI conventions as the rest of the
author's projects. Licence Apache-2.0 WITH LLVM-exception, as every SPDX
header says. REUSE adoption: SPDX headers on every source file now; a
`REUSE.toml` and `LICENSES/` directory when the first file arrives whose
licence differs.
**Why:** One word, like the sibling repositories. The Copier origin is
recorded in `.copier-answers.yml` so `copier update` can pull template
changes later.
**Log:**

- 2026-10-15 — Decided.

---

## toolchain-pin

**Question:** The Lean 4 release and Batteries revision, and the commit of
the cplusplus/draft repository that stands for the C++26 text and anchors
every citation.
**Status:** DECIDED 15 October 2026.
**Decision:** Lean `leanprover/lean4:v4.35.0` (`lean-toolchain`), Batteries
`v4.35.0` (`lakefile.toml`, `lake-manifest.json`). The draft pin is recorded
once, in `Overload.Std.draftPin`, and reported by `lake exe citations --pin`;
see [draft-pin](#draft-pin).
**Why:** The latest stable release of each on the day the repository was
created. The draft pin lives in Lean rather than in a side file so that the
citation index, the drift check and the installed C++ package
(`overload::draft_pin()`) cannot disagree about it.
**Log:**

- 2026-10-15 — Decided.

---

## explicit-instance-routes

**Question:** Which ways of supplying an instance other than canonical
lookup does the model cover?
**Status:** DECIDED 16 October 2026.
**Decided by:** the author.
**Decision:** Both. First the library as written: the operation object
with its `const auto &` instance parameter, the user-side pinning
pattern, and the by-value trailing argument. Then the plan's three
routes, as alternative designs, so the guidance can compare them.
**Why:** The library is what the theorems have to be about. The plan's
routes are designs someone might adopt, and the inheritance guidance is
stronger when it can say which of them a leak depends on.
**Facts recorded 16 October 2026,** from beman.transpose (the typeclass
repository's `include/beman/transpose/`):

- Each named operation is its own operation object (`fmap`, `replace`,
  `bind`, `join`, and the applicative and fold objects), and each object
  has one `operator()`. It looks the
  instance up through a trailing `const auto &TC` constant template
  parameter defaulted to the lookup, constrained on the call through
  `TC`. There are no overloads between routes, no priority tags and no
  rank types. The library's own comment calls naming `TC` explicitly "a
  curiosity, not an API".
- What the plan called the three routes appear as patterns, not as
  overloads. An instance can be called directly (`tc.fmap(f, v)`). User
  code can pin one through its own `const auto &` constant template
  parameter defaulted to the lookup. A few objects take one by value as a
  trailing function argument: `traverse` takes a `POLICY` that defaults
  to the applicative lookup and is constrained by `applicative_object_for`,
  and `fold_map` and `combine_all` have an extra-arity overload taking a
  monoid. Library-provided instances take others as type template
  parameters and default-construct them (`lifted_monoid`, the Kleisli
  monoid).
- Constant template parameters for instances are references bound to the
  `inline constexpr` lookup variables, never structural values. Instance
  types are empty. Monoids may carry state, and are passed by value only.
- No instance is conditioned on another instance at a subterm, so lookup
  never recurses.

**Log:**

- 2026-10-16 — Opened. The plan's argument-identity suspect, leak 4 and
  the structural-identity obligation assume instances are passed as
  structural values. The library passes them as references, so template
  argument identity is the identity of the referenced object
  ([temp.type]/2 for references), not value equivalence. The model's
  `Val` covers values only.
- 2026-10-16 — Decided. The model gains `Ty.ref`, a reference constant
  template argument whose identity is the designated object, and
  `Ty.removeCvref`. The operation object is emitted and computed as four
  call cases (`op_object_*` in `Overload/Typeclass/Emit.lean`).
- 2026-10-17 — The two user-side routes are modelled. Pinning is
  `pinTemplate`, after `fmap_plus_one` in the library's
  `examples/transpose/lookup_modes_example.cpp`, with an instance object
  outside lookup (`Decl.object`) to pin. The by-value route is
  `byValueObject`, `traverse`'s `POLICY` reduced to `fmap`, with
  `Ty.typeOf` for `std::remove_cvref_t<decltype(...)>` and an atomic
  shape constraint in place of `applicative_object_for`. Nine emitted
  cases (`pin_*`, `by_value_*`). The plan's three routes remain.
- 2026-10-17 — The plan's three routes are modelled as an alternative
  design: `valueRoute`, `typeRoute` and `argumentRoute` in
  `Overload/Typeclass/Routes.lean`, beside the canonical object in one overload
  set, as eight emitted call cases (`routes_*`). Call cases gain explicit
  template arguments. Non-template functions in a call with explicit
  template arguments are out of the fragment; no case has one.
- 2026-10-21 — Phase 10 gives the routes' constant parameters their
  conversion: `valueRoute`'s `auto` takes the argument's own type, and a
  derived instance value and the base's own are one specialization under
  a base-typed parameter (`slicing_identifies`); `pinTemplate`'s
  reference denotes the object (`reference_keeps_identity`).

---

## scope-syntax

**Question:** How do scopes enter the program syntax?
**Status:** DECIDED 20 October 2026.
**Decision:** A scope is a field. Each namespace-scope declaration
(`Decl.function`, `Decl.functionTemplate` through `FunctionTemplate`,
`Decl.class`, `Decl.classTemplate`, `Decl.object`) carries `scope :
Scope := []`, a path of namespace and class steps from the global scope
outward in. A member function is a function whose scope ends in its
class; `Decl.class` gains no member list. An object carries the name of
its class, so a call on it has a scope to search for `operator()`. The
program stays a flat list, lookup is a layer in front of `resolve`, and
the found declarations are handed to the existing resolution with
`Candidate.index` their position in the found list, as `generate`
numbers candidates today.
**Why:** Counted against the sources on 20 October 2026: eleven pattern
sites on `Decl.function`, fifteen on `Decl.functionTemplate`, five on
`Decl.class`, two on `Decl.object`, two exhaustive matches, eight
inductions on the candidate list and none on the program, and about
fifteen theorems that reason positionally on the flat list
(`declaredBeforeUse`, `stability`, the verdicts of `Units`,
`call_stability_unit`). A field with a default leaves every program
literal, every induction and every positional theorem as it is. A nesting
constructor `Decl.namespace (decls : Program)` breaks the positional
theorems and makes every new structural proof a nested recursion. A side
table or enter-and-leave markers make a declaration's scope a function of
its prefix, so every insertion lemma would need a balanced-markers
hypothesis. A member list on `Decl.class` is a nested inductive again and
breaks `eraseBases`, `directBases` and `allBases`.
**Decided by:** the author, on the design review of 20 October 2026.
**Facts recorded 20 October 2026:** an omitted trailing default field in
a Lean pattern elaborates to the default value, not a wildcard, so `|
.function _ _ => true` is false on a namespaced function. Every existing
match on a declaration therefore gets an explicit placeholder, and a
guard checks that a namespaced function is seen, because the compiler
will not say.
**Log:**

- 2026-10-20 — Decided.
- 2026-10-20 — Landed. `ScopeStep`, `Scope` and the fields are in
  `Overload/Program.lean`; every existing program literal, proof and
  emitted case is unchanged, as the counts predicted. One correction on
  the way: two declarations are one entity only when they also declare
  the same kind (`sameEntity`), or an object and a function of one name
  would merge instead of conflicting.

---

## integer-widths

**Question:** What are the ranges of the fragment's integer types?
**Status:** DECIDED 21 October 2026.
**Decision:** LP64 with `char` signed: `bool` 0 to 1, `char` and `signed
char` 8 bits, `short` 16, `int` 32, `long` and `long long` 64, and the
unsigned types to match. `bool` is an integer type ([basic.fundamental]/11)
with that range, so a conversion to it from a constant other than 0 or 1
is narrowing, which is what GCC and Clang do.
**Why:** The Standard fixes only minimum ranges and leaves the widths
implementation-defined ([basic.fundamental]/4). The draft's own example
assumes `signed char` cannot represent 1000, and the emitted cases are
compiled on LP64 platforms. The table is `Overload.integerTypes`, tagged
with this entry; a compiler that treats a `bool` target otherwise is a
finding, not a change to the table.
**Decided by:** the author, on the plan of 21 October 2026.
**Log:**

- 2026-10-21 — Decided.
- 2026-10-21 — Landed: `Overload.integerTypes` carries this tag. The
  emitted cases for `bool`, `unsigned` and `long` targets agree with GCC
  and Clang.

---

## value-typing

**Question:** Does a constant template argument value carry its type?
**Status:** DECIDED 21 October 2026.
**Decision:** No. `Val` stays an untyped tree. The source type of an
explicit value is the literal's by [lex.icon]/3 for an integer, `bool`
for a `bool`, and the class for a class value (`Val.sourceType`).
Deduced values are not converted and not typed: [temp.deduct.type]/20,
which requires the type of a deduced `i` to equal the parameter's type
in the specialization it was deduced from, stays uncovered.
**Why:** Typing `Val` would reach into every deduction proof for a rule
the typeclass encoding never exercises: its constant parameters are
references to the lookup variables and `auto`, and the explicit-instance
routes pass class values. Out of the fragment for the same reason:
floating-point values, pointers and pointers to members, arrays,
enumerations, unions, closure types, user-defined conversions and
converting constructors, braced-init-lists, `decltype(auto)`
parameters.
**Decided by:** the author, on the plan of 21 October 2026.
**Log:**

- 2026-10-21 — Decided.
- 2026-10-21 — Landed: `Val.sourceType` and `literalType` in
  `Overload/Arguments.lean`. `narrowing_constant` is the reason the
  typing is not missed: for a constant, the source type decides nothing
  the value does not (`findings.md`).
- 2026-10-24 — Phase 14 restates the class value: a `Val.obj` lists the
  class's elements, bases then members ([dcl.init.aggr]/2), and
  `Program.uniqueValue` is `Option Val`, some only for a class whose
  elements are all classes with one value. With a scalar or reference
  element a class has as many values as the element, and the result a
  converting constructor gives for one is a value the model cannot
  compute: `candidateInitializer` answers none, which `convertArg` reports
  as a soft failure, and `Env.initializer` is the oracle a layer above
  supplies, as phase 11 first planned. The library's instance types have
  no members and keep their one value (`instance_is_aggregate`).
- 2026-10-23 — User-defined conversions and converting constructors
  leave the out-of-fragment list: phase 11 models them as declarations
  by type (`user-defined-conversions`), and the copy-initialization of
  a class-typed constant parameter through one is a case of
  `convertArg`.

---

## user-defined-conversions

**Question:** How are converting constructors and conversion functions
represented, when the fragment has no expressions?
**Status:** DECIDED 23 October 2026.
**Decision:** As declarations. `Decl.converting cls conv` declares for a
ground class a single-argument constructor by its parameter type or a
conversion function by its target type, each with its `explicit` flag
([class.conv.ctor]/1, [class.conv.fct]/2, /4). The initialization
context is a flag, `Init`, copy or direct: a call argument and a
candidate initializer are copy-initialization ([dcl.init.general]/13),
and direct-initialization exists only as the contrast that admits
explicit candidates ([over.match.ctor]/1). The value a converting
constructor gives a class-typed constant parameter is the environment's
candidate-initializer oracle, `Env.initializer`, which the program
computes as the class's one value: a class value in the fragment lists
its base subobjects and nothing else, so no constructor body is needed
(`findings.md`).
Out of the fragment: constructor templates and conversion function
templates ([over.ics.user]/3), conversion functions returning a
reference, list-initialization and aggregates, the ellipsis sequence,
conversions to non-class types other than the identity, virtual
conversion functions, and access to a conversion.
**Why:** The questions the phase answers are about viability, rank,
deduction and identity, and each is decided by the types and the
`explicit` flag alone. A separate declaration keeps the flat program
and every match on `Decl.class`. Casts are expressions and stay out
with the rest of the expression language (`expression-depth`); what
`explicit` does is a property of the initialization context, which the
flag carries.
**Decided by:** the author, on the plan of 23 October 2026.
**Log:**

- 2026-10-23 — Decided.
- 2026-10-23 — Landed, in six stages merged the same day. `Decl.converting`,
  `UserConv`, `Init` and `Program.userConversions` in stage 2; `Ics`,
  `Program.ics`, `IcsForms`, `ics_iff`, `betterIcs`, `BetterIcs` and
  `betterIcs_iff` in stage 3, with the ranking brought forward from
  stage 4 because `Program.ranking` needs it; the ambiguous-sequence
  check in `Program.call`, `standard_beats_user_defined` and eleven
  emitted cases in stage 4; `Program.candidateInitializer`,
  `deduction_ignores_conversion`, `explicit_never_implicit` and
  `conversion_identifies` in stage 5; `Overload/Typeclass/Conversion.lean`
  in stage 6. Two departures from the plan: no `Env.userConvert`, since
  the candidate initializer is computable (above), and a correction to
  phase 10, a value for a placeholder reference parameter now refused
  (`findings.md`). `inheritance_erasure` gained the hypothesis that the
  program declares no user-defined conversion, harvested as the
  refinement-by-shape obligation.

---

## function-types

**Question:** Does `Ty` get function types?
**Status:** DECIDED 24 October 2026.
**Decision:** Yes, one constructor, `Ty.fn params ret`, with `params` a
`nil`/`cons` chain ([basic.compound]/1). Deduction treats it
structurally, as `spec`; the forms `T()` and `T(T)` of
[temp.deduct.type]/8 are in scope already. Functions keep the return
type they have (`FunctionTemplate.ret`, defaulting to `void`), and
`Decl.function` gains one. No pointer-to-member types, no
noexcept in the type, no ref-qualifiers.
**Why:** `is_invocable`, `is_function`, a compound requirement's
return-type-requirement and the primary type categories all need a
function type to name, and a trait fragment without one would answer
`is_function` by fiat. The change touches every induction over `Ty`,
so it is made first in phase 12, while nothing depends on it, and
once.
**Decided by:** the author, on the plan of 24 October 2026.
**Log:**

- 2026-10-24 — Decided.

---

## special-member-fragment

**Question:** Which of the special member function rules are in the
fragment?
**Status:** DECIDED 24 October 2026.
**Decision:** The six kinds of [special]/1 for classes with public
non-static data members and public bases: implicit declaration and its
suppression ([class.default.ctor]/1, [class.copy.ctor]/6, /8,
[class.copy.assign]/2, /4, [class.dtor]/2), the parameter form
([class.copy.ctor]/7, [class.copy.assign]/2), defined as deleted
([class.default.ctor]/2, [class.copy.ctor]/10, [class.copy.assign]/7,
[class.dtor]/7), triviality ([class.default.ctor]/3, [class.copy.ctor]/12,
[class.copy.assign]/9, [class.dtor]/8), eligibility ([special]/6),
explicitly defaulted and deleted ([dcl.fct.def.default]/1, /5,
[dcl.fct.def.delete]/1, /2), const-default-constructible
([dcl.init.general]/7) and the usable candidate ([over.match.general]/4).
A user-declared special member is a declaration by kind, body and the
`const` of its parameter; it is public and unconstrained.
Out: unions and anonymous unions, variant members, arrays, bit-fields,
virtual functions and virtual bases, inherited constructors and
using-declarations, exception specifications, constexpr-suitability,
the by-value copy assignment operator, ref-qualifiers and explicit
object parameters, `volatile`, and the access of a user-declared
special member.
**Why:** Every deletion rule is a rule about a member or a base
subobject, decided by overload resolution over the subobject's class
and the usable-candidate check, which the model has. What is out is
either a kind of entity the fragment lacks (unions, arrays, virtual
functions) or a property of a function the fragment does not carry
(exception specifications, constexpr). A private copy constructor was
the idiom for an uncopyable class before `= delete`; the fragment keeps
`= delete` and leaves access on special members for a later question.
**Decided by:** the author, on the plan of 24 October 2026.
**Log:**

- 2026-10-24 — Decided.

---

## trait-residue

**Question:** Which type traits does the model compute, and which stay
with the oracle?
**Status:** DECIDED 24 October 2026.
**Decision:** Computed, as `Program.trait`: the primary and composite
categories the fragment inhabits ([meta.unary.cat]/3,
[meta.unary.comp]/2, by [basic.types.general]/6, /7 and
[basic.compound]/1), with the uninhabited ones false; `is_const`,
`is_same`, `is_base_of`; `is_convertible` ([meta.rel]/6);
`is_constructible` and its default, copy and move forms
([meta.unary.prop]/9); `is_assignable` on class types and its copy and
move forms; `is_destructible`; the `is_trivially_` forms;
`is_trivially_copyable` and `is_standard_layout` ([class.prop]/1, /2);
`is_empty`; `is_invocable` and `is_invocable_r`. The transformations
`remove_const`, `remove_reference`, `remove_cvref` and
`add_lvalue_reference` are functions on `Ty`.
Residue, as `Constraint.atomic` strings for the oracle: the
`is_nothrow_` forms, `is_aggregate` and `is_implicit_lifetime`,
`is_swappable`, `has_unique_object_representations`, layout
compatibility and alignment, `is_signed` and `is_unsigned`,
assignment to non-class types, and any expression that is not a call.
**Why:** A trait is computed when its defining paragraph is a rule
about types, special members or a call the model already decides, so
that its answer is a theorem of those rules and is differentially
tested against the compilers' own trait. A trait stays with the oracle
when it needs a property the fragment does not carry. The residue is
named so that a constraint written with it is visibly an assumption.
**Decided by:** the author, on the plan of 24 October 2026.
**Log:**

- 2026-10-24 — Decided.
- 2026-10-24 — Stage 4 landed, `Overload/Traits.lean`. One more residue:
  `is_invocable` of a class callee, since the call on an object is
  resolved above the environment that answers traits; a function type or
  a pointer to one is computed. The environment answers a trait atom
  from the program (`Env.ofProgram`'s `traits`, default `Program.trait`),
  and `inheritance_erasure` takes the trait oracle as a parameter.
- 2026-10-25 — Compound and nested requirements landed. One residue of
  the same kind: whether a braced initialization `T{args}` is
  potentially throwing, which a compound requirement's
  noexcept-specifier asks. For a call the answer is the selected
  function's exception specification and its parameters'
  initializations ([except.spec]/6); for a braced initialization the
  model answers softly, so `{ T{} } noexcept;` makes the
  requires-expression `false`.
- 2026-10-25 — The class-callee residue of 2026-10-24 is closed.
  `Env.fullWithin` answers `is_invocable` and `is_nothrow_invocable` of
  a class callee one level down, as it answers a requires-expression:
  the call on the object over the class's call operators
  (`Program.objectInvoke`, [func.require]/1, [over.call.object]/1),
  in the environment below (`Program.traitAbove`). The base
  environment, `Env.ofProgram`, still answers it softly, so a trait of
  a class callee nested deeper than the program is long is not
  satisfied. Still residue: surrogate call functions
  ([over.call.object]/2), and a class template specialization as
  callee, because the fragment has no class template members and the
  trait inherits that.
- 2026-10-25 — Surrogate call functions are in ([over.call.object]/2,
  `Program.surrogates`), and with them the implied object argument: a
  call on an object resolves over its call operators carrying their
  implicit object parameter, `const X&` for the fragment's const members
  ([over.match.funcs.general]/2 to /4, `Decl.withImplicitObject`), and
  its surrogates, with the object first in the argument list
  ([over.call.object]/3, `impliedObject`; `declval<Fn>()` for the
  trait). A member call `obj.f(args)` still leaves the object out. That
  the implicit object parameter changes no resolution over const call
  operators alone is stated as a target theorem, not proved; the
  concrete programs decide it. Still residue: conversion functions
  declared in a base class, which neither the sequences nor the
  surrogates see, and the fragment's want of class template members,
  which a specialization callee inherits.
- 2026-10-25 — The two notes above first said "a class template
  specialization as callee", a symptom. The cause is that the fragment
  has no class template members, so a specialization has no call
  operators to find. Phase 15 is the plan to give it them
  (`docs/plan.md`, phase 15); the residue closes when its
  specialization-lookup stage lands.
- 2026-10-26 — Closed. Phase 15's specialization-lookup stage keys the
  member search by type and instantiates the template's declarations
  for a specialization, so `classCallee` returns the type and
  `is_invocable` of a specialization callee is the call on the object
  through its call operators and surrogates
  (`specialization_callee_invocable`). Still residue: conversion
  functions declared in a base class.

---

## value-nature

**Question:** How does the model speak of value and reference semantics
as properties of a type, when the Standard has no term for them?
**Status:** DECIDED 24 October 2026.
**Decision:** As definitions and theorems, never rules. `Program.valueNature
c` holds when every special member of `c` is defaulted and non-deleted;
`Program.referenceMember c` when some subobject, through class-typed
members and bases likewise, is of reference type or `const` type, a
`const` member of class type included. `value_nature_iff` connects them
for every class whose special members are the rules' own
(`Program.implicitClass`): one that declares no special member and no
conversion, whose class-typed subobjects are such classes to any depth;
`value_nature_flat` is the case without class-typed subobjects. The
author's names for the two natures, data and codata, appear
in the docs; the Lean names are `valueNature` and `referenceMember`,
and no `@[std rule]` cites a sentence for either, since none exists.
A pointer is data: a scalar, trivially copyable, deleting nothing. Its
codata aspect, aliasing of the pointee, is a property of the object
model, which the fragment does not have, and the model does not state
it.
**Why:** The Standard renders the idea exactly, through the deletion
rules for reference and `const` members and their propagation through
subobjects, so a theorem says what a rule would have to invent. Naming
the limit at pointers keeps the model from claiming a semantics it
cannot check.
**Decided by:** the author, on the plan of 24 October 2026.
**Log:**

- 2026-10-24 — Decided.
- 2026-10-24 — Stage 3 landed. A `const` member without a default member
  initializer deletes the default constructor as a reference member does
  ([class.default.ctor]/2 with [dcl.init.general]/7), so the reference
  nature is a reference or `const` member, not a reference member alone.
  Proved for flat classes (`deleted_flat`, `value_nature_flat`,
  `pointer_member_keeps_value_nature`).
- 2026-10-24 — Stage 6 landed. On the encoding's programs, an instance
  type with no data members has value nature and is trivially copyable,
  empty and standard-layout (`instance_shape_regular`), and one holding
  a reference is structural for the value route and not assignable
  (`reference_member_instance`): structural and value nature are
  different properties.
- 2026-10-25 — The general theorem landed. `implicit_deleted` is the
  induction over fuel: for a class whose special members are the rules'
  own, the copy assignment is deleted exactly when the class has a
  reference member, the destructor never, and with no reference member
  nothing is. It rests on seven lemmas, `resolveCtor_nullary`,
  `resolveCtor_lvalue`, `resolveCtor_rvalue_move`,
  `resolveCtor_rvalue_copy`, `resolveAssign_lvalue`,
  `resolveAssign_rvalue_move` and `resolveAssign_rvalue_copy`, which
  say what overload resolution over a class's implicit members selects
  for each argument a subobject supplies: the move member for an rvalue
  of the class, by [over.ics.rank]/3, and the copy member for an rvalue
  of the `const` class or when the defaulted move member is defined as
  deleted and so is not a candidate. `value_nature_iff` and
  `copy_assignment_deleted_iff` state the result at the program's fuel;
  `deletion_propagates` is the one-step form per kind. Two corrections
  to the definition on the way. A `const` member of class type counts
  as a reference member, since [class.copy.assign]/7 deletes the
  assignment through it as through a `const` scalar. The definition
  reads the potentially constructed subobjects rather than the members,
  so a base falls under the same clause. The theorem needs the
  declarations well-formed (`subobjectsWellFormed`: a base is a class
  type, a member's type has one `const` at most), which is a property
  of the program's shape and not a rule. Eleven emitted trait cases
  observe the propagation, the `const` class-typed member and the
  fallback to the copy constructor; GCC 15 and Clang 24 agree on all.

---

## semantic-requirements

**Question:** How does the model represent what a concept requires
beyond its constraint, the semantic requirements of
[res.on.requirements]/1 and the typeclass laws?
**Status:** DECIDED 24 October 2026.
**Decision:** As named statements nothing decides. `Semantic` is a slug
and a statement in words, cited at the paragraph that gives it where the
Standard does; `Decl.semantic concept law` attaches one to a concept's
specification. `Laws := Semantic → List Ty → Prop` is the oracle, a
hypothesis a theorem states, never a function the model computes.
`Program.models` is satisfaction of the concept's normal form and every
law of its specification and of the concepts it is defined in terms of.
A case claims laws as it claims atomics, and `Program.modelVerdicts`
gives the ill-formed-no-diagnostic verdict of [res.on.requirements]/2 at
a use whose selected candidate's constraint names a concept that is
satisfied with a law unclaimed. `#owes decl` lists the laws in a
declaration's closure. The typeclass laws are `Semantic`s with their
source in the statement and no citation, since the Standard does not
state them. No law is encoded as a decidable property.
**Why:** A law is a statement about values, and the fragment has no
expressions to evaluate; encoding one as a predicate would be a second,
unverified transcription of the same prose. What the model can give is
what the Standard's own framework gives: one name, one citation, the
distinction between satisfying and modelling, and the verdict that says
the compiler cannot catch the difference. Listing which theorems owe
which laws is what the obligations table was for; the audit makes the
list a consequence of the proofs.
**Decided by:** the author, on the plan of 24 October 2026.
**Log:**

- 2026-10-24 — Decided.
- 2026-10-24 — Landed, in five stages merged the same day: `Semantic`,
  `Decl.semantic`, `Program.laws`, `Program.models` and the verdict in
  stage 2; the library's concepts with their laws in stage 3; the
  typeclass laws and `superclass_coherence_owed` in stage 4. The large
  normal forms are decided in the kernel (`decide +kernel`), resting on
  `propext` alone. The algebraic laws, excluded from the obligations
  table at the start, are its last section now.

---

## virtual-fragment

**Question:** Which of the virtual function rules are in the fragment?
**Status:** DECIDED 24 October 2026.
**Decision:** A member function is virtual, pure virtual or final by a
field of its declaration, or by overriding a base's virtual function,
which is correspondence of the declarations ([class.virtual]/1, /2); a
destructor likewise. Polymorphic and abstract classes, the final
overrider along single inheritance, the ill-formed override of a `final`
function and the `override` that overrides nothing, the loss of
triviality, standard layout and emptiness, the unconstructible abstract
class and the ill-formed by-value parameter of abstract type. Out:
virtual base classes and the unique final overrider across them,
covariant return types, `final` on a class, the definition requirement of
[class.virtual]/12, and the dynamic type: a call is resolved at the
static type, where the derived class's override is what lookup finds.
**Why:** The traits and the special member rules need to know whether a
class is polymorphic and which functions are virtual, which declarations
decide. What a virtual call does at run time is behaviour, and the model
has none; what it selects at compile time is the lookup phase 9 already
has.
**Decided by:** the author, on the plan of 24 October 2026.
**Log:**

- 2026-10-24 — Decided.
- 2026-10-24 — Stage virtual-functions landed, `Overload/Virtual.lean`.
  `Virt` has five values: `override` joined the planned four, since
  [class.virtual]/5, the `override` that overrides nothing, has nothing
  to check without it; a function declared `override` is virtual only
  through the function it overrides. The abstract-class checks rest on
  the normative rules the note [class.abstract]/3 points to: [basic.def]/5
  for `is_constructible`, since `T t(args)` defines an object;
  [expr.call]/7 for the by-value parameter at a call; and
  [dcl.fct.def.general]/2 for `is_convertible`, whose test function is a
  definition with the destination as its return type. A pure destructor
  is in: it makes its class abstract, and a derived class's destructor
  overrides it without being pure. The virtual functions a class's
  objects have are computed as its final overriders, the class's own
  declared or overriding functions and the bases' no member overrides;
  with no virtual bases, two bases' functions of one signature are two
  final overriders of two subobjects, which is well-formed.

---

## exception-specification-fragment

**Question:** How are exception specifications represented?
**Status:** DECIDED 24 October 2026.
**Decision:** As a predicate on every function ([except.spec]/1):
`noexcept : Option Bool` on each function-like declaration, `none` for no
specifier, and `noexcept : Bool` on the function type. A user-provided
function without a specifier is potentially throwing; a destructor or a
defaulted special member without one has the implicit specification of
[except.spec]/7 to /9, decided through the operation resolution selects
for each subobject, in the facts beside deletion. The `is_nothrow_`
traits are the base trait and the selected operation non-throwing. Out:
`noexcept` with a dependent expression, the `noexcept` operator, the
throw-expression and the other potentially-throwing expressions, since
the fragment's expressions are calls, and deallocation functions.
**Why:** The whole `is_nothrow_` family is one rule over the predicate,
and the predicate's implicit cases are the special member machinery once
more. A constant `noexcept(true)` or `noexcept(false)` is what the
fragment's declarations can carry; a dependent one is an expression.
**Decided by:** the author, on the plan of 24 October 2026.
**Log:**

- 2026-10-24 — Decided.
- 2026-10-24 — Stage exception-specifications landed. The implicit rule
  is `Program.throwingWithin`, beside `trivialWithin` and shaped like it,
  with the facts at the fuel below for the resolution and its own
  recursion for the subobjects' members; it is not a field of `Facts`,
  since deletion and triviality never consult it. A default member
  initializer is an expression the model does not have, so `Member`
  carries `throwingInit`, whether the initializer may throw, and the
  emitter spells one as a call to a potentially-throwing function. On
  the function type the specification is a `Bool`, and deduction
  requires the two to agree; the function pointer conversion of
  [temp.deduct.call]/4, by which a pointer to a `noexcept` function
  deduces against a parameter without one, is out of the fragment with
  the rest of the conversions on deduced pointers. `is_nothrow_swappable`
  with a `swap` the program declares is left to the oracle, since the
  call's lookup is above the environment. The destructor's case of
  [except.spec]/5, a `noexcept(false)` destructor overriding a virtual
  one, is not checked: `virtualsWellFormed` sits below the implicit
  specifications in the layering, and the fragment's destructors say
  `noexcept(false)` only to be found by the traits.

---

## aggregate-fragment

**Question:** Which aggregates and which aggregate initializations are in
the fragment, and what is a class value?
**Status:** DECIDED 24 October 2026.
**Decision:** A class is an aggregate by [dcl.init.aggr]/1 on its
declarations: no constructor declared, no protected base, not
polymorphic, and every member public as the fragment has them. Its
elements are its direct bases then its members ([dcl.init.aggr]/2), and
a class value, `Val.obj`, lists exactly those: the value is the
aggregate. Brace initialization from a list of argument types, with `{}`
for the unlisted elements and a reference without an initializer a
failure ([dcl.init.aggr]/4, /6); parenthesized aggregate initialization
when no constructor is viable ([dcl.init.general]/15); value-initialization
of a non-aggregate by its default constructor. Out: arrays, designated
initializers, anonymous unions, brace elision, inherited constructors.
`uniqueValue` and `candidateInitializer` hold for classes whose elements
are classes with one value; a converting constructor's result for a
class with scalar members is the environment's oracle.
**Why:** Phase 11's "one value per class" was true of classes without
members and is false with them, and the aggregate's element list is what
the model's values were already shaped as. `T{}` and `T t;` differ for an
aggregate with a `const` member, which phase 13 had merged.
**Decided by:** the author, on the plan of 24 October 2026.
**Log:**

- 2026-10-24 — Decided.
- 2026-10-24 — Stage aggregates landed, `Overload/Aggregate.lean`. One
  more exclusion: narrowing in list-initialization, since the
  initializers are types and narrowing is a property of a value. The
  simple requirement `T{args};` is its own requirement form,
  `Constraint.Requirement.braceInit`, since a requires-expression's
  expression is otherwise a call. Value-initialization of the elements a
  parenthesized aggregate initialization leaves out is `valueInit`
  ([dcl.init.general]/8): a scalar is zero-initialized, a class
  default-initialized by a usable default constructor, a reference
  cannot be. GCC 15's library has no `is_implicit_lifetime`
  (`findings.md`); Clang 24 agrees with the model on every case.

---

## class-template-members

**Question:** How does the fragment represent the members of a class
template, and what does a specialization have?
**Status:** DECIDED 25 October 2026.
**Decision:** A class template has bases, possibly dependent, and its
members, special members and conversions are declarations for the
current instantiation, the class template's name followed by its head's
parameters ([temp.dep.type]/1, [temp.decls.general]/2); its member
functions and member function templates are declarations in its scope,
which is a class scope ([basic.scope.class]/1). A member template's own
parameters follow the class's in the numbering ([temp.mem]/1). A
specialization has the template's member declarations with its
arguments substituted, computed when the specialization is looked into
and nowhere else ([temp.inst]/2, /3, [temp.mem.func]/2,
[temp.res.general]/1), and its point of instantiation precedes the
first declaration that refers to it ([temp.point]/4). Out: explicit and
partial specializations of class templates and their members
([temp.expl.spec]/6, [temp.spec.partial.member]/1), member definitions
outside the class, static data members, member classes, friends,
dependent names inside a template's own definition, the incomplete type
of an undefined template, and the several points of instantiation of a
member function specialization.
**Why:** The fragment's class templates were empty, so a specialization
had no members for any search to find, and `is_invocable` of a
specialization callee inherited that as residue. The encoding's
derivation base is a class template with constrained member templates
and a dependent protected base, and the model stood in for it with a
plain class and an oracle for the member call. The substitution of the
specialization's arguments into the template's declarations is what the
Standard calls the implicit instantiation of declarations, and the
fragment has no definitions, so it is the whole of instantiation. The
encoding's instances are partial specializations of a variable
template, which the model has had since phase 1, so class template
specializations other than the primary's have no consumer.
**Decided by:** the author, on the plan of 25 October 2026.
**Log:**

- 2026-10-25 — Decided.
- 2026-10-26 — Stage template-members landed. The specialization key
  (`Program.classKey?`) completes the argument list against the head
  by kind and default, and neither forms a default nor converts a
  constant argument: that is `validType`'s check, in the environment,
  and the member search below the environment needs only the
  arguments. A member of a class, with no arguments, is its declaration
  unsubstituted (`instantiate_ground`). The derivation bound stays the
  program's length, so a chain through specializations nested deeper
  than the program is cut off; no program of the fragment approaches
  it. `inheritance_erasure` assumes no class template declares a base
  (`Program.templatesBaseFree`): erasure is not extended to
  specializations, as the plan said.
- 2026-10-26 — Stage specialization-lookup landed. For the point of
  instantiation, a declaration refers to a specialization only with
  ground arguments (`Decl.mentionsSpecOf`): the current instantiation,
  and any dependent specialization, is referenced from a templated
  context, whose point is the enclosing specialization's, out of the
  fragment. The member call `obj.f(args)` now leads with the object
  (`Program.memberCallOn`); the fragment's members being `const`, no
  earlier case moved. An object of specialization type is not
  declarable, `Decl.object` naming a class, so the call on one is
  observed as `is_invocable`.
- 2026-10-26 — Stage derivation-base landed. An instance may declare
  the type of its value (`Decl.instance`), which enters only where a
  member call on the value resolves: the lookup's value keeps its name
  `instance_of<a, i>` in deduction, so nothing about the lookup moved.
  A member-call requirement forms its types through the environment
  and reads the object's class through the lookup when
  `remove_cvref_t<decltype(TC)>` names one
  (`Program.lookupValueType`). The derivation base is the class
  template it is, and the operation object's constraint is the header's
  requires-expression, resolved; the abstract object's oracle
  (`memberAtomics`) stays as the specification the earlier theorems are
  about, agreeing with the computation exactly where the
  implementation's member is accurate.
- 2026-10-26 — Stage class-template-docs landed; the phase is closed.
  [temp.inst]/10 and [temp.spec.general]/4 stay in scope without a
  counterpart: the first says an instantiation that resolution does not
  need may not happen, which no theorem rests on, and the second
  defines a specialization.
