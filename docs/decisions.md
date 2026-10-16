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

---

## lookup-scope

**Question:** Is name lookup, including argument-dependent lookup, in the
model?
**Status:** DECIDED 13 October 2026.
**Decision:** No. Whatever is found outside the model is not part of the
model. A customization point object such as `fmap` that dispatches to an
instance is in the model, as a fixed candidate set. A member such as a
hypothetical `std::vector::fmap`, or a delegation to `ranges::transform`,
is outside it and enters only as an opaque candidate.
**Log:**

- 2026-10-13 — Decided.
- 2026-10-15 — `Program.candidates` is the candidate set: the declarations
  with the callee's name, in order.

---

## ranking-fidelity

**Question:** Is implicit conversion ranking a parameter or a modelled
mechanism?
**Status:** DECIDED 13 October 2026, subject to the separability theorem.
**Decision:** A parameter for the core theorems. Dispatch is user-written,
so constraint exclusion, `if constexpr` chains and priority tags will all
occur. One concrete ranking, covering priority tags and reference binding,
is supplied so the model can say which styles are safe.
**Log:**

- 2026-10-13 — Decided.

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

---

## instance-inheritance

**Question:** May instance types for related typeclasses be related by
inheritance?
**Status:** OPEN; settled by inheritance erasure and superclass coherence in
phase 6.
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

---

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

---

## p3606-mode

**Question:** Does the model transcribe the C++26 text, under which
deduction runs for every template candidate, or the P3606 rule, under which
a perfect non-template match suppresses it?
**Status:** OPEN.
**Default:** The text, with the P3606 rule as a flag on the resolution
relation so both can be stated and compared. The two differ exactly on the
step-order hazard, and GCC implements P3606 today.
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
