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
  `differential/known-disagreements.txt` for Clang 17 to 20.
  Update, 17 October 2026: the same ordering shows with a function
  parameter. In `sfinae_requires_shields.cpp` the requires-clause is not
  satisfied, so the text never substitutes the parameter whose type
  instantiates a lookup that fails hard. Clang 17 to 20 substitute it and
  report the error. Clang 21 to 24 and GCC 13 to 16 shield it.

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
  overload, as the model does. GCC 13 to 15 still report ambiguity, and
  so does Clang 17, so the known entries remain for GCC and for Clang 17
  and 18.

- **An ambiguous instance is a deduction failure on both compilers**
  (16 October 2026). `op_object_ambiguous_hard.cpp` is the operation
  object of beman.transpose at a type two instances match, with neither
  more specialized, beside a worse fallback template. [temp.spec.partial.match]/1
  makes the ambiguous use ill-formed. The matching is how the
  specialization is instantiated, and [temp.deduct.general]/8 puts
  instantiations outside the immediate context, so the model makes the
  call ill-formed. GCC 13 to 15 and Clang 17 to 24 select the fallback.
  The result depends on how the lookup is spelled. A hand-written variant
  that looks up through a class template's static member is a hard error
  on GCC and soft on Clang. Through a variable template whose initializer
  names that static member, it is hard on GCC and on Clang 18, and soft on
  Clang 23. For the library this means that two unordered instances do
  not make a call ill-formed in practice. The type is silently treated as
  having no instance, and another overload, if there is one, is chosen.
  That is the silent choice coherence rules out for lookup itself.
  Listed in `differential/known-disagreements.txt` for both compilers;
  the verdict stands on the text.
  Update, 17 October 2026: the by-value route behaves the same way.
  `by_value_ambiguous_hard.cpp` defaults the policy type to
  `std::remove_cvref_t<decltype(functor<...>)>` at an ambiguous type,
  and GCC 13 to 16 and Clang 17 to 24 all select the fallback.
  So does `routes_type_ambiguous_hard.cpp`, where the ambiguous lookup is
  the canonical overload's default, reached through a call meant for the
  plan's type route. Under the text that call is ill-formed; on every
  compiler it selects the type route.

## About the model

- **Deduction is most general only without nested references** (17
  October 2026). On the first-order fragment deduction is matching, and
  it finds the least bindings that solve `P = A` (`deduceTy_most_general`).
  A reference inside `P` breaks this: `T&` against `int&` deduces `T` as
  `int`, but `T` as `int&` solves it too, by reference collapsing
  (`OverloadTest/Deduction.lean`). Deduction's answer is the one the form
  `T&` of [temp.deduct.type]/8 gives. It is not the only solution. A call strips the
  top-level reference before deducing, so only references nested inside
  a parameter type fall outside.

- **The function type is substituted parameters first** (17 October
  2026). Substitution proceeds in lexical order ([temp.deduct.general]/7),
  and the model forms a template's parameter types before its return
  type, the order of a trailing return type. A leading return type comes
  first lexically: emitted as one, `enable_if` was checked before the
  parameter's hard error and every compiler accepted the call. The
  emitter now spells a return type with a condition as a trailing return
  type. A leading return type with a condition is outside the model.

- **The derived-class exclusion is vacuous on the fragment** (17 October
  2026). [temp.deduct.call]/4 excludes a possible deduced `A` that is a
  base of another possible one. Every possible deduced `A` has the form of
  a class template specialization, and the fragment gives class templates
  no bases, so the exclusion never fires. `deduceFromBase` implements it,
  and the draft's own example, which needs variadic templates, is out of
  reach. Two bases of the same form fail deduction, as /5 says, on every
  compiler (`temp_deduct_call_5_two_bases.cpp`).

- **Deduction and ranking share one conversion relation** (17 October
  2026). The environment's convertibility check for non-dependent
  parameters ([temp.deduct.general]/5, sentence 8) had been identity up
  to cv and references. A priority tag in a template's non-dependent
  parameter then failed deduction instead of converting to its base. The
  environment now asks the program's ranking whether an implicit
  conversion sequence exists (`Program.ics`), so a fallback at a lower tag
  is viable (`priority_tag_fallback.cpp`).

- **More-specialized is a strict partial order as far as searched** (16
  October 2026). Irreflexivity and asymmetry are theorems
  (`moreSpecialized_irrefl`, `moreSpecialized_asymm`). Transitivity was
  searched over every triple of single-parameter templates drawn from 18
  parameter shapes, 5832 triples, with no counterexample
  (`OverloadTest/Ordering.lean`); a proof is still owed.
  Update, 17 October 2026: proved for templates of type parameters whose
  parameter types have no reference, with any number of parameters
  (`moreSpecialized_trans`). Ten of the eighteen searched shapes are in
  that fragment. The proof needed the synthesized types to be a
  constructor of their own, `Ty.synth`, so that a match against them can
  be undone. With names, as before, undoing it would have meant parsing
  the name. The reference shapes are still evidence only.
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

- **A protected base does not hide the implementation** (17 October
  2026). `derive_functor<Impl>` inherits `Impl` protected, which reads as
  keeping `Impl` out of view. Overload resolution does not see access:
  implicit conversion sequences ignore it ([over.best.ics.general]/2), and
  deduction from a derived class goes through the protected base. A
  function that names `Impl`, or a class template `Impl` comes from, is
  selected for an instance type built on it, and the call is ill-formed
  at the conversion ([conv.ptr]/3, [dcl.init.ref]/4). It is not merely
  not viable, so no other overload is tried
  (`protected_base_selected_ill_formed`,
  `protected_base_deduced_ill_formed`, `access_protected_base_*.cpp`).
  Every compiler agrees. Within a requires-expression the same access
  failure is part of substitution, so a constraint that tests such a call
  is simply false.

- **A reference to the lookup does not separate units** (17 October
  2026). The plan expected divergence-separation to hold where the
  instance is a template argument of the function and to fail where it
  is looked up inside a body. The canonical operation object takes the
  instance as a template argument, but as `const auto &TC =
  functor<...>`, a reference to the lookup variable. A reference argument
  is the entity it designates, and the variable `functor<box<int>>` is
  one entity in every unit, whatever its initializer selects. So two
  units whose lookups select different instances deduce one
  specialization (`operation_object_not_separated`), and the program
  gives one function two meanings, ill-formed with no diagnostic
  required ([basic.def.odr]/16). Pinning names the instance object and
  separates. The by-value policy names the instance's type, and separates
  only when instances have distinct types (`byValue_separated`), which is
  an obligation of its own (`obligations.md`). The verdict at the lookup
  itself comes first: the program is already ill-formed with no
  diagnostic required where a use cannot reach an instance another unit
  selects (`missing_instance_verdict`).

- **Priority tags check every condition** (17 October 2026). The plan
  expected the three dispatch styles to select the same candidate and to
  differ only in whether having no candidate is soft or hard. Over the
  eight valuations of three conditions they select the same one
  (`dispatch_styles`). With none, exclusion and priority tags leave the
  call not viable and the if-constexpr chain is ill-formed, as expected
  (`dispatch_*_none.cpp`). They also differ in which conditions are
  checked. The if-constexpr chain stops at the first condition that holds,
  and so does exclusion written with the negations first, since a
  conjunction is checked left to right. Priority tags check every
  overload's condition, because each overload is a candidate. With the
  first condition holding and the last one failing hard when checked,
  exclusion and the chain select the first, and the tagged call is
  ill-formed (`dispatch_hard_condition`, `dispatch_*_hard_last.cpp`).
  Every compiler agrees. For the typeclass encoding this matters when a
  later condition looks an instance up through a lookup that can fail
  hard. The library's lookups default to `std::false_type`, so they
  cannot.

- **sfinae-requires holds up to step order and subsumption** (17 October
  2026). The plan said an `enable_if` encoding and a requires-clause with
  the same condition give the same viable set and differ only where
  ordering consults subsumption. For `enable_if` in a trailing return
  type the viable set is the same, and so is resolution where ordering
  does not change (`sfinae_requires`, `sfinae_requires_resolve`).
  Ordering does change where a requires-clause wins by subsumption: the
  `enable_if` form has no constraint, and the call is ambiguous
  (`sfinae_loses_subsumption`, `sfinae_requires_subsumes.cpp`,
  `sfinae_enable_if_unordered.cpp`). The two also differ in step order,
  which the plan did not predict. A requires-clause is checked before the
  function type is substituted. `enable_if` in a trailing return type is
  checked while it is substituted, after the parameters, so a hard error
  in a parameter's type is reached that the requires-clause would have
  shielded (`sfinae_unshielded`, `sfinae_enable_if_unshielded.cpp`).
  Every compiler agrees on the encodings. Clang 17 to 20 do not shield
  even with the requires-clause, by the ordering filed under
  [compiler disagreements](#compiler-disagreements).

- **Constraint-promotion fails as stated** (17 October 2026). The plan
  said that turning a Mandate into a constraint changes the outcome only
  by removing that candidate. Where the Mandate fails, it does: the call
  resolves as if the declaration contributed nothing
  (`constraint_promotion`, `constraint_promotion_falls_back.cpp`). Where
  the Mandate holds, the candidate stays, but its constraint has grown,
  and partial ordering compares constraints. A template that lost to a
  more constrained sibling can then tie with it. With one template
  requiring `class_like` and another carrying the Mandate `empty_like`,
  the first is selected. Removing the second changes nothing. Promoting
  its Mandate makes the call ambiguous (`promotion_reorders`,
  `constraint_promotion_before.cpp`, `constraint_promotion_reorders.cpp`).
  Every compiler agrees. The theorem holds when the promoted constraint
  changes no ordering against the other candidates, and when checking the
  Mandate never fails hard: promoted, a hard error there would make every
  call that deduces the template ill-formed. Mandate-inertness holds with
  no hypothesis (`mandate_inertness`). A Mandate never falls back: the
  more specialized template is selected and its unmet Mandate makes the
  call ill-formed (`mandate_no_fallback.cpp`).

- **Inheritance erasure holds at exact type** (17 October 2026). The plan
  predicted that inheritance between instance types is selection-inert
  exactly when every use takes the instance at its deduced exact type. The
  model proves the "if" direction (`inheritance_erasure`). A class is
  touched when it is erased or derived from an erased class. If every
  conversion the call can form has the same class on both sides whenever
  either side is touched, then erasing the bases changes nothing:
  candidates, viability, ranking and the result. Priority tags and other
  untouched classes may still convert. The hypothesis is about the
  conversions, not the signatures, because a template parameter deduced
  from one argument can meet another argument of a derived type. The
  "only if" direction holds by counterexample: a function that names the
  base instance type accepts the derived one, and after erasure it
  accepts nothing (`erasure_needs_exact_type`,
  `erasure_named_base_*.cpp`). Deduction from a derived class is the
  second way erasure changes an outcome, leak 2: a parameter
  `const derive_functor<I>&` deduces `I` from a Monad instance type
  derived from `derive_functor<opt_impl>` (`derived_class_deduction`,
  `leak_derived_deduction_*.cpp`). So the theorem also asks that no
  argument of a touched class meet a dependent parameter of class
  template form (`NoDerivedDeduction`). Access checking is not modelled.

- **Separability holds with no hypothesis on the ranking** (17 October
  2026). The plan expected the instance selected to be invariant under
  the choice of ranking. It is, for any two rankings of any conversion
  types: if both select the candidate at one position, they select the
  same candidate, specialization and template arguments included
  (`separability`). Candidates are generated, and their template
  arguments deduced and converted, before any conversion sequence is
  ranked. The ranking decides only which candidate wins, and that it does
  decide: `ranking_live` is a call that the program's ranking resolves and
  the identity ranking finds no viable function for. The plan's
  rank-precedence suspect is the general form: a worse conversion for any
  argument loses whatever the non-template preference and partial
  ordering say (`separability_rank_precedence`).

- **Leak 1 is live** (17 October 2026). An overload that names an
  Applicative instance type concretely, `use(const applicative_i&)`, wins
  over a generic `use(const T&)` at that type, by the non-template
  preference. At a Monad instance type derived from it, the generic
  template wins: an exact match beats a derived-to-base conversion, and
  conversions are compared first (`rank_beats_refinement`,
  `leak_rank_exact.cpp`, `leak_rank_derived.cpp`). Every compiler agrees.
  Deriving one instance type from another moves the call to the less
  refined overload. The obligation is exact-type use
  ([obligations](obligations.md)).

- **The plan's routes separate, but the type route is exposed** (17
  October 2026). The canonical overload and the three routes as one
  overload set, `fmap`, select the intended overload for each call form
  (`routes_*.cpp`). Explicit template arguments bind the leading
  parameters, so the instance comes first in the two template-parameter
  routes. The value route and the argument route are protected from the
  canonical lookup: the canonical overload fails at the explicit
  argument's kind, or at the extra call argument, before its default is
  substituted. The type route is not. The canonical overload takes the
  instance type as its `F`, deduces `T`, and substitutes its default, so
  at a type whose canonical lookup is ambiguous the call is ill-formed
  although the caller supplied an instance (`routes_type_ambiguous_hard`).
  The argument route cannot keep a default, as the library's by-value
  route does: beside the canonical overload the two are unordered and a
  call without the policy is ambiguous
  (`routes_argument_default_ambiguous`). The library avoids both by giving
  each named operation one operation object with one `operator()`, so
  there is no overload set of routes.

- **Soft failure is by construction only where the route constrains**
  (17 October 2026). The plan expected a missing instance to fail as a
  constraint by construction. That holds for the operation object, whose
  constraint is the call through the instance (`fmapObject_outcome`). It
  holds for the by-value route only through the shapeless-default
  obligation: the policy type of a missing instance is
  `std::false_type`, and the constraint fails because that type has no
  `fmap` (`byValue_omitted_outcome`). The pinning pattern in the
  library's examples has no constraint at all. A missing instance binds
  the primary, the call is viable, and the error is in the body
  (`unpinned_deduce`, `pin_missing_viable.cpp`). Both compilers agree.
  The obligation falls on whoever writes a pinning function, not on the
  typeclass author.

- **Explicit instances never instantiate the lookup** (17 October 2026).
  A pinned instance and a passed policy are used in place of the
  default, so the canonical lookup is not instantiated. The outcome is
  the same in every program, including one where the canonical lookup is
  ambiguous (`pinned_deduce`, `byValue_passed`, and the two
  `*_explicit_ambiguous.cpp` cases). The two routes differ in identity.
  A pinned instance enters the specialization as the object it
  designates, and a passed policy as its type, so two policies of one
  type with different state give one specialization. The
  instance-in-the-type obligation is by construction for pinning, and
  not for the by-value route once an instance carries state, as the
  library's monoids may.

- **The library has no explicit-instance overloads** (16 October 2026).
  The plan's three explicit-instance routes and its dispatch-styles
  theorem assume operation objects that offer several ways in. In
  beman.transpose each named operation (`fmap`, `replace`, `bind` and the
  rest) is its own operation object, and each such object has one
  `operator()`, which looks the instance up through a trailing `const
  auto &` constant template parameter. The instance, the bundle of
  operations, is a different object, reached through the lookup. The other routes are user-side patterns or a by-value
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
  Update, 17 October 2026: at the call surface (`call_stability`) soft
  failure is a hypothesis, the soft primary, as expected. The single
  translation unit assumption is not a hypothesis. It is built into the
  model's environment, which consults every instance the program declares
  wherever the call is, so the theorem cannot see the order of
  declaration against use. Phase 8 removes it from the environment.
  Update the same day: per unit, a call sees only what precedes it
  (`call_stability_unit`). An instance declared after the call cannot
  move it. It can only make the program ill-formed with no diagnostic
  required, which the model reports and stops at
  (`late_insertion_verdict`).
  The theorem also needs the other candidates not to consult the lookup,
  which the plan did not foresee. It holds for non-template functions
  outright.

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
