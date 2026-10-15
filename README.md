# Modelling C++ overload resolution in Lean

A Lean 4 model of the C++ selection mechanisms that the pure-library
typeclass technique depends on: template argument deduction, substitution
failure, constraints, partial ordering, partial specialization matching and
overload resolution. The typeclass encoding of
[beman.typeclass](https://github.com/bemanproject/typeclass) is defined on
top of the model, and its properties are proved about that definition.
The plan is in [`docs/plan.md`](docs/plan.md); it is the charter for the
work and the phases are tracked there.

Every rule in the model cites the sentence of the Standard it transcribes,
as a checked attribute:

```lean
@[std rule "temp.deduct.type#4.sentence-4"]
def allDeduced (arity : Nat) (σ : Bindings) : Bool := ...
```

A build fails when a rule is uncited or an axiom untagged. The index of
what rests on each sentence is generated into
[`docs/citations.md`](docs/citations.md), and `make drift-check` confirms
every citation against the pinned draft (N5054, tag `n5054`).

## Status

Phase 0 is closed and phase 1 is open; see the status note under *Phases*
in `docs/plan.md`. Three probes, run before any Lean existed, are in
`probes/` with their results and verdicts in
[`docs/probes.md`](docs/probes.md). Decisions, open and settled, are in
[`docs/decisions.md`](docs/decisions.md). Findings about the Standard, the
compilers or the plan are in [`docs/findings.md`](docs/findings.md).

## Layout

```txt
Overload/            the model: Std (citation attribute), Syntax, Outcome,
                     Deduction, Program, Emit (C++ emitter), Lint
Overload.lean        imports everything and runs the citation lint and audits
OverloadTest/        #guard tests, run by `lake test`
Tools/               lake exe citations (the index), lake exe emit (the C++)
src/smd/overload/    the typeclass encoding under study, as C++, with tests
src/examples/        a runnable example of the encoding
probes/              the hand-written C++ probes and their runner
scripts/             drift-check.sh, differential.sh
differential/        known compiler disagreements on emitted programs
docs/                plan, decisions, probes, findings, citations
papers/wg21          the vendored WG21 paper framework (git subtree)
infra/               Beman CMake infrastructure (git subtree)
```

## Building

The Lean side needs [elan](https://github.com/leanprover/elan); the
toolchain is pinned in `lean-toolchain` and Batteries in `lakefile.toml`.
The C++ side needs a C++23 compiler, CMake and Ninja, which `uv` installs
into a local `.venv` (`make venv`); Catch2 is fetched at configure time.

```shell
make                  # configure, build and run every test, C++ and Lean
make lean-test        # the Lean model and its tests only
make citations        # regenerate docs/citations.md from the environment
make drift-check      # every citation exists in the pinned draft
make differential     # emit the model's C++ and compile it with g++ and clang++
make probes           # rerun the hand-written probes
make lint             # pre-commit: clang-format, gersemi, markdownlint, codespell, ...
make help             # the rest
```

`PROBE_COMPILERS="g++-13 clang++-18" make differential probes` picks the
compilers; `TOOLCHAIN=gcc-15` and `CONFIG=RelWithDebInfo` pick the C++
toolchain and configuration as in the sibling projects.

## Provenance

The repository was generated from the
[steve-downey/example](https://github.com/steve-downey/example) Copier
template (`.copier-answers.yml`) and keeps its Makefile, CMake, pre-commit
and CI conventions; `copier update` can pull later template changes. The
reference implementation of what is modelled is
[bemanproject/typeclass](https://github.com/bemanproject/typeclass).

## License

Apache-2.0 WITH LLVM-exception. The code in `infra/` is Apache 2.0 from the
[Beman Project](https://github.com/bemanproject/infra); `papers/wg21` carries
its own licence.
