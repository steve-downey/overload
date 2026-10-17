# CLAUDE.md

Guidance for Claude Code when working in this repository.

## What this is

A Lean 4 model of C++ template argument deduction, substitution, constraints,
partial ordering and overload resolution, built to prove properties of the
typeclass encoding in [bemanproject/typeclass](https://github.com/bemanproject/typeclass).
Read `docs/plan.md` first: it is the charter, with phases, target theorems,
suspects and obligations. `docs/decisions.md` is the decision log; every
`@[assumed "..."]` tag names an entry there. `docs/findings.md` collects what
the work has turned up, and `docs/obligations.md` the obligations harvested
from the theorems. Do not restate those documents elsewhere; link to
them.

## Two sides, one Makefile

- **Lean** lives at the root: `lakefile.toml`, `Overload/`, `OverloadTest/`,
  `Tools/`. `lake build` builds the model and runs the citation lint and the
  axiom audits in `Overload.lean`; `lake test` runs the `#guard` tests.
- **C++** is the Copier-generated layout from steve-downey/example: `src/`,
  `CMakeLists.txt`, `infra/`, `etc/`, `installtest/`, `papers/wg21`. The
  library `src/smd/overload/encoding.hpp` is the typeclass encoding under
  study, reduced to the fragment the model covers; keep it a faithful
  reduction of beman.transpose, never a rival design.
- `make` (default `test`) runs both. `make lint` runs pre-commit, which is
  the source of truth for formatting. `make help` lists the rest.

`.copier-answers.yml` records the template origin. This repository is not
itself a template: there is no `template/` directory and no round-trip
check to keep in sync.

## Citation discipline

Every rule cites the Standard, as an attribute, by stable name and
paragraph and where possible sentence: `@[std rule "temp.deduct.type#8.sentence-1"]`.
On a constructor the attribute goes on an `attribute [std rule "..."] Ctor`
command right after the inductive, because Lean rejects attributes in
constructor declarations. A `@[specification]` inductive is a specification
relation or outcome type; every one of its constructors must be cited or the
build fails. An axiom must carry `@[assumed "slug"]`, and the slug must be a
section of `docs/decisions.md`.

- Roles: `rule` for a normative sentence taken as given, `theorem` for a
  sentence proved from the others, `note` and `example` for non-normative
  text used as a proof target or a test.
- Count sentences the way eel.is anchors them. The pinned text is tag
  `n5054` of cplusplus/draft (`Overload.Std.draftPin`); `make drift-check`
  verifies every cited section and paragraph exists, and
  `make drift-check-current` reports paragraphs that differ on the draft's
  `main`.
- After adding or changing citations run `make citations` and commit
  `docs/citations.md`; CI fails if it is stale.
- Headline theorems are audited with `#audit` in `Overload.lean`. A `sorry`
  is an axiom and fails the audit. Do not leave `sorry` anywhere: drop the
  theorem rather than ship it unproved.

## Model conventions

- Each mechanism is given twice, as an inductive relation and as an
  executable function, with an agreement theorem (`decisions.md#spec-style`).
  Rules are inductive relations, never Lean axioms.
- `Ty` is one inductive type; template argument lists are its `nil`/`cons`
  constructors and a constant argument is `Ty.value`. This is deliberate
  (see the docstring of `Overload/Syntax.lean`): it keeps every proof an
  ordinary `induction`. Use `Ty.spec'` and `Ty.args` for the readable
  spelling. `Val` is laid out the same way.
- Template parameters are positions in the template head (`ParamIdx`).
- Names are the Standard's where it has one: `P`, `A`, deduced `A`,
  immediate context, viable, more specialized.
- Lean core plus Batteries only; no Mathlib (`decisions.md#library-dependency`).

## Differential testing

`Overload/Emit.lean` turns cases into C++ translation units whose
`static_assert`s check the model's expectation in unevaluated contexts.
`make differential` emits them and compiles each with every compiler in
`PROBE_COMPILERS` (default `g++ clang++`). A disagreement is a finding
against the cited sentence: describe it in `docs/findings.md`, then list it
in `differential/known-disagreements.txt` so CI stays green. Never settle a
disagreement by majority.

A deduction case's expectation must be what `deduceTemplate` computes and
a call case's what `resolve` computes under `Mode.text` with the
program's ranking, `Program.ranking` (`OverloadTest/Emit.lean` checks both); a raw case states
its expectation by hand and says so in its `source` field. `Mode.p3606` is
the switch of `decisions.md#p3606-mode`; the compilers are what they are,
so an emitted case always states the text's expectation.

## Probes

`probes/` holds the hand-written C++ probes from the plan, reconstructed
from its descriptions; `docs/probes.md` records which cells reproduce. Keep
them compiling on GCC 13 and Clang 18 with `-std=c++23`, since those are
the versions the plan's table was made on.

## Prose

Docs follow the author's voice: short declarative sentences, concrete
nouns, no stock transitions or enthusiasm words, state the result first and
expand below it. A decision-log entry is Question / Status / Decision / Why
/ Log, with a slug named for the question.
