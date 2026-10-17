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

- **Subsumption is not a partial ordering** (16 October 2026). False
  statement, in a note. [temp.constr.order]/2 says "The subsumption
  relation defines a partial ordering on constraints." It is reflexive
  and transitive, but `A ∧ B` and `B ∧ A` subsume each other and are
  different constraints, so it is a preorder
  (`Constraint.subsumes_not_antisymm`). It is a partial order on
  constraints taken up to mutual subsumption, which is presumably what is
  meant. Normative text is unaffected: every use of subsumption in
  ordering asks for one direction and not the other.

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
  replaced; Clang implements the new order from version 21, and Clang 20 still
  fails the example (checked 16 October 2026); the model transcribes
  the text, and `OverloadTest/Steps.lean` shows the same call is a hard
  error when the constraint step is skipped. Listed in
  `differential/known-disagreements.txt` for Clang up to 20.

- **GCC's shortcut is narrower than P3606 as the model reads it** (16
  October 2026). `draft_temp_constr_atomic_3_better_match.cpp` is the
  draft's example in [temp.constr.atomic]/3: `f(0)` with a non-template
  `f(int)` and a template whose constraint fails hard when checked. The
  text makes the call ill-formed, and the model's `.p3606` mode makes it
  well-formed, since `f(int)` is a perfect match and the template would
  never be deduced. GCC 13 rejects it, as the text says, while compiling
  the two emitted hazard cases, where the hard error is in a default
  template argument rather than in constraint satisfaction. So whatever
  GCC skips for a perfect match, it is not the whole of deduction. Not a
  disagreement with the model under `.text`; recorded against
  `decisions.md#p3606-mode` as evidence about what the P3606 wording
  needs to say.

- **Clang 21 implements the model's P3606 reading in full** (16 October
  2026). Clang 18 to 20 agree with the text on all three cases above.
  Clang 21 to 24 compile all three: `step_order_hazard.cpp`,
  `step_order_hazard_guarded.cpp`, and the draft's [temp.constr.atomic]/3
  example. So once a non-template is a perfect match, Clang skips
  deduction for the template, constraint satisfaction included. That is
  what `Mode.p3606` computes, and it goes further than GCC 13 to 15,
  which still reject the constraint case. The two implementations
  disagree about what P3606 covers. Listed in
  `differential/known-disagreements.txt` for Clang 21 to 24; recorded
  against `decisions.md#p3606-mode`.

- **Neither compiler ignores a placeholder's type-constraint when
  comparing template parameters** (16 October 2026).
  `tie_break_placeholder_constraint.cpp` is the tie-break probe's variant
  C as the model spells it: two overloads differing in a defaulted
  constant template parameter declared `auto` in one and `shape auto` in
  the other, the second more constrained. [temp.over.link]/6 says
  equivalence of constant template parameters ignores type-constraints on
  placeholder types, so the parameters are equivalent, the gate of
  [temp.func.order]/8 is open, and the model selects the more constrained
  overload (`PartialOrdering.paramEquivalent`). GCC 13 and Clang 18 both
  report the call ambiguous. This is the plan's divergence 2 with a
  different Clang result from the one the plan recorded for its own,
  unrecovered, probe source (`probes.md`); the by-value spelling here is
  the one Clang 18 accepts. Listed as known for both compilers; the
  verdict stands on the text.
  Update, 16 October 2026: Clang 19 to 24 select the more constrained
  overload, as the model does. GCC 13 to 15 still report ambiguity, so
  the known entries remain for GCC and for Clang 18.

## About the model

- **More-specialized is a strict partial order as far as searched** (16
  October 2026). Irreflexivity and asymmetry are theorems
  (`moreSpecialized_irrefl`, `moreSpecialized_asymm`). Transitivity was
  searched over every triple of single-parameter templates drawn from 18
  parameter shapes, 5832 triples, with no counterexample
  (`OverloadTest/Ordering.lean`); a proof is still owed.
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

- **The draft's first matching example reproduces** (16 October 2026).
  The five uses in the first example of [temp.spec.partial.match]/2,
  including a constant template parameter and the ambiguity between #3
  and #5, come out as the draft says (`OverloadTest/Typeclass.lean`).

## About the plan

- **The library has no explicit-instance overloads** (16 October 2026).
  The plan's three explicit-instance routes and its dispatch-styles
  theorem assume operation objects that offer several ways in. In
  beman.transpose each operation object has one `operator()`, which looks
  the instance up through a trailing `const auto &` constant template
  parameter. The other routes are user-side patterns or a by-value
  trailing argument on `traverse` and `fold_map`. Instance constant
  parameters are references, not structural values, so the plan's
  argument-identity analysis does not apply to the library as written,
  and nothing needs termination today: no instance requires another.
  Recorded in `decisions.md#explicit-instance-routes`, which is open.

- **Subsumption implies satisfaction only up to hard errors** (16 October
  2026). The subsumption-sound target said subsumption implies
  satisfaction-implication. With hard errors in the outcome it holds only
  in the form "if `P` subsumes `Q` and `P` is satisfied, `Q` is satisfied
  or checking it is a hard error" (`Constraint.subsumes_satisfied`).
  `A` subsumes `B ∨ A`, and checking `B ∨ A` evaluates `B`, which
  checking `A` never touched (`Constraint.subsumes_satisfied_hard`). The
  target is restated in the plan's table.

- **Stability of lookup needs neither expected hypothesis** (16 October
  2026). The plan expected stability to need soft failure of a missing
  instance and the single translation unit assumption. For the
  variable-template lookup it needs neither: `stability` holds for any
  program and any insertion point. A missing instance there is just the
  primary. Both hypotheses belong to the call surface, where a lookup is
  instantiated during deduction and its outcome becomes soft or hard, and
  where order of declaration against use matters. They will reappear
  when stability is stated for calls.

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
