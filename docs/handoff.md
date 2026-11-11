# Handoff

The state of the work at the last session's end, for the next session to
read after `plan.md`. Rewritten when a phase closes; the dated line says
which.

## Where things stand, 11 November 2026

Phase 16, the object model, is open with stages 1, 2, 5, 6 and 7 landed on
the branch `claude/cpp-object-model-lean-gec6xk`. Fifteen phases are closed
before it. `Overload/Object/*.lean` is the object model: storage,
bytes, objects and their lifetime, pointers, the abstract machine of
nineteen operations, the access judgement in both forms with
`access_iff`, the `std::launder` and `std::start_lifetime_as` theorems,
the definition rule of the initialization profile with `not_sound` and
`not_complete`, and P4222R3's full rule set as a checker
(`Overload/Object/P4222.lean`) with the paper's examples reproduced and
the table of traces on which it and the object model disagree, and the
proposed wording P4416R0 as a rule set of the same checker
(`Overload/Object/P4416.lean`), its examples reproduced and its changes
to the table proved, and functions with bodies as traces, so that the
call-site attributes are checked and the callee run
(`Overload/Object/Functions.lean`).
`OverloadTest/Object.lean` holds the guards. Every theorem is a
`decide`. `Overload/Object/Emit.lean` has twenty differential cases
with constant evaluation as the oracle; `make differential
PROBE_COMPILERS="g++-13 clang++-18"` agrees except for the six filed in
`findings.md` and `differential/known-disagreements.txt`.

## What is owed

Recorded in `plan.md`, phase 16, stages 2 to 4, and the status entry:

- A run of the object-model cases on GCC 15 and Clang 24, which this
  session did not have: four of the six disagreements are GCC 13's
  alone.
- The relation forms of creation, destruction and assignment
  (`decisions.md#spec-style`, log of 11 November 2026).
- The periods of construction and destruction, where the profile meets
  constructors that read members.
- The author's reading of `decisions.md#initialization-profile`: the
  four readings the checker fixes where P4222R3 leaves room, aliasing
  above all.
- Constructor bodies (P4222R3 §5.1, P4416R0 [profiles.init.class]/1),
  which need the period of construction: stage 4.

The owed items of phase 15 stand as `plan.md` records them.

## What comes next

Stage 3 of phase 16, the relation forms, then the author's reading of the profile entry and
the findings' open question about `std::start_lifetime`. The open areas
list of `plan.md` is unchanged: Applicative and Monad need parameter
packs and the expression fragment; the object model is now the place a
typed expression fragment would get its lvalues from.

## How the work runs

A phase is planned from the pinned draft (`n5054`, clone at
`~/src/cplusplus/draft`) into `plan.md` with a cross-reference table,
design, stages and decisions; "Begin" runs every stage, each on its
own branch merged `--no-ff` after the full check set; docs close the
phase; push only when asked. Conventions are in `CLAUDE.md`.
