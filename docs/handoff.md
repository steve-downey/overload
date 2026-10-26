# Handoff

The state of the work at the last session's end, for the next session to
read after `plan.md`. Rewritten when a phase closes; the dated line says
which.

## Where things stand, 26 October 2026

Fifteen phases are closed, through phase 15, class templates and their
members. `main` is at `2bf5e73` plus this note, pushed to `origin`.
Every check passes: `lake build`, `lake test`, `make citations` (661
citations, two in-scope paragraphs uncovered, both definitional),
`make drift-check-current` (six known editorial drifts), `make
differential PROBE_COMPILERS="g++ clang++-24"` (all cases agree with
GCC 15 and Clang 24), `make lint`.

The model covers deduction, substitution outcomes, constraints, partial
ordering, overload resolution with user-defined conversions, declarations
and lookup, template argument conversion, the type categories, special
members, traits, requires-expressions, semantic requirements, virtual
functions, exception specifications, aggregates, and class templates with
bases and members. The typeclass side declares the encoding of
beman.transpose, now part of beman.typeclass, through Functor: lookup,
the explicit-instance routes, superclass retrieval, the derivation base
as a class template, and the operation object's constraint as a resolved
member call.

## What is owed

Recorded in `plan.md`'s theorem table and the phase status entries:

- The general member-template-arguments theorem; shown on one program.
- The inertness of the implicit object parameter for a class whose call
  operators are all `const`.
- Erasure assumes no class template declares a base.
- The abstract oracle `memberAtomics` stays as the specification the
  early theorems are about; the resolved constraint is the header's.

Residue: conversion functions declared in a base class
(`decisions.md#trait-residue`).

## What comes next

`plan.md`, section "Open areas, to be picked up next": the list of what
the fragment lacks, ordered by weight, with the order to take it in.
The target is Applicative and Monad, then sender/receiver of
`std::execution`. Those need parameter packs first and a typed
expression fragment with computed return types second; translation
units are the area that changes what is already proved.

## How the work runs

A phase is planned from the pinned draft (`n5054`, clone at
`~/src/cplusplus/draft`) into `plan.md` with a cross-reference table,
design, stages and decisions; "Begin" runs every stage, each on its
own branch merged `--no-ff` after the full check set; docs close the
phase; push only when asked. Conventions are in `CLAUDE.md`.
