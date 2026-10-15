# Findings

What the model has turned up about the Standard, the compilers, or the
plan. Four kinds of finding about the Standard can result:

| Finding | How it appears in the model |
|---|---|
| Redundancy | A normative sentence is proved from the other rules. Benign, and it shows which statements carry the weight. |
| Gap | No rule applies to a well-formed input, so the relation is partial where the executable function must still answer. |
| Conflict | Two rules give different outcomes for one input. Determinism fails, with both derivations as the witness. |
| False statement | A note, example or claimed property is refuted by the rules. |

Ambiguity is not a conflict. The Standard makes it a defined outcome, and
the model keeps it as a value. A disagreement between compilers is a
separate matter, filed under test-oracle (decisions.md#test-oracle).

## Against the Standard

None yet.

## Compiler disagreements

The three from the probes are in `probes.md`, with verdicts. Disagreements
on emitted programs are listed in `differential/known-disagreements.txt`
and described here as they arrive.

None on emitted programs yet.

## About the plan

- **Attributes on constructors** (15 October 2026). Lean 4 does not allow
  an attribute in a constructor's declaration (`Attributes cannot be added
  to constructors`), so the plan's sketch `| @[std rule "..."] ok : ...` is
  not available. A citation on a constructor is written as an `attribute`
  command directly after the inductive, `attribute [std rule "..."]
  Subst.ok`, and the lint checks the same thing. The spelling on
  definitions and theorems is as sketched.
- **Probe reconstruction** (15 October 2026). The probe sources had to be
  reconstructed; step-order B and tie-break C did not reproduce at first,
  and tie-break C still does not. Details in `probes.md`.
