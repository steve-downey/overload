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

- **GCC skips deduction for template candidates when a non-template is an
  exact match** (16 October 2026). `step_order_hazard.cpp` and
  `step_order_hazard_guarded.cpp` emit the plan's step-order suspect: a
  defaulted constant template parameter whose default instantiates a
  lookup that fails hard, beside a non-template exact match. The model,
  transcribing [over.match.funcs.general]/8 and [temp.deduct.general]/5
  sentences 2 and 3, expects the program to be ill-formed, and so does
  Clang 18. GCC 13 compiles both, which is the P3606 behaviour recorded in
  `probes.md` (divergence 1). Listed in `differential/known-disagreements.txt`
  for GCC; the model gains a switch for the P3606 rule once its wording
  settles (decisions.md#p3606-mode).

- **Clang 18 checks non-dependent conversions before constraints** (16
  October 2026). `draft_temp_deduct_general_5_step_order.cpp` is the
  draft's own second example of [temp.deduct.general]/5, verbatim but for
  the assertion. For `f(zz, 42)` the text fails deduction for #1 at
  sentence 7, `C<int>` not satisfied, before sentence 8 would check the
  conversion of `zz` to `void*`. Clang 18.1 checks the conversion first:
  it substitutes into `ZZ`'s conversion function template, instantiates
  `Z<void>`, and reports a hard error, so the draft's well-formed example
  does not compile. GCC 13 compiles it. This is the ordering CWG2369
  replaced, which Clang implements from version 20; the model transcribes
  the text, and `OverloadTest/Steps.lean` shows the same call is a hard
  error when the constraint step is skipped. Listed in
  `differential/known-disagreements.txt` for Clang up to 19.

## About the model

- **The draft's step-order example reproduces, and shows why the order
  matters** (16 October 2026). In the second example of
  [temp.deduct.general]/5, `f(zz, 42)` fails deduction for #1 because
  `C<int>` is not satisfied. `OverloadTest/Steps.lean` checks that the
  same call with the constraint removed is a hard error: the conversion of
  `zz` to `void*` would then be checked, and it instantiates `Z<void>`
  through the conversion function template's default argument. The
  constraint check, sentence 6, runs before the conversion check, sentence
  8, and that order is what keeps the example well-formed;
  `constraint_soft_shields_function_type` is the general statement.

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
