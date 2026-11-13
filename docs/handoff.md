# Handoff

The state of the work at the last session's end, for the next session to
read after `plan.md`. Rewritten when a phase closes; the dated line says
which.

## Where things stand, 11 November 2026

Phase 16, the object model, is open with stages 1 to 7 landed on
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
(`Overload/Object/Functions.lean`), and constructor bodies with the
period of construction (`Overload/Object/Construction.lean`).
`OverloadTest/Object.lean` holds the guards. Every theorem is a
`decide`. `Overload/Object/Emit.lean` has twenty-two differential cases
with constant evaluation as the oracle, run on GCC 13 and Clang 18 (in the
earlier cloud session; on the author's machine Clang 18 selects
libstdc++ 16, which it cannot parse, so only GCC 15 and Clang 24 run
there) and on GCC 15 and Clang 24; the disagreements are filed in `findings.md`
and `differential/known-disagreements.txt`. Three const complete cases
are kept but not emitted, since libstdc++ 15 rejects `construct_at` on
a const pointer.

## What is owed

Recorded in `plan.md`, phase 16, stages 2 to 4, and the status entry:

- The relation forms of the machine's remaining clauses: casts,
  `launder`, `start_lifetime_as`, `memcpy`, the block operations,
  `activate` and `construct` (`decisions.md#spec-style`).
- The period of destruction, delegating constructors, constructors with
  parameters, exceptions in constructors, and members of class type
  with constructor bodies of their own (`decisions.md#construction-period`).
- The author's reading of `decisions.md#initialization-profile`: the
  four readings the checker fixes where P4222R3 leaves room, aliasing
  above all.
- Constructor bodies (P4222R3 §5.1, P4416R0 [profiles.init.class]/1),
  which need the period of construction: stage 4.

The owed items of phase 15 stand as `plan.md` records them.

## What comes next

The author's reading of the profile entry and
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
