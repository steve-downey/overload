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
The design note at the end draws one lesson from all four sections.

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
  for GCC; the model carries the P3606 rule as a switch beside the text,
  and keeps both while the proposal is open (decisions.md#p3606-mode).

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

- **GCC still rejects a derived value for a base-typed class constant
  parameter** (21 October 2026). `derived_to_base_value.cpp` is
  `struct B {}; struct D : B {}; template <B> void f(); f<D{}>()`, and
  `routes_value_sliced.cpp` is the plan's value route with its instance
  parameter typed as the pinned instance's class and a derived instance
  supplied. [temp.arg.nontype]/3, as P2308R1 rewrote it in November
  2023, introduces `constexpr T v = A;` for a class type `T`, so the
  argument is sliced to its `B` subobject and the parameter's value is
  `B{}` (`convertArg`, `slicing_identifies`). Clang 24 slices it and
  agrees with the model on both cases. GCC 13 to 16 reject the argument
  as a conversion not permitted in a converted constant expression,
  which is the rule before P2308R1, the text of C++20 and C++23. This is
  the constant-argument probe of `probes.md` reproduced from the model;
  the verdict there stands. Listed in `differential/known-disagreements.txt`
  for GCC. Every other conversion case, the draft's narrowing example
  included, agrees on both compilers.

## About the model

- **A sixth cited paragraph differs on the draft's main, editorially**
  (24 October 2026). With phase 14's citations `make drift-check-current`
  reports [class.virtual]/2 beside the five known: a comment in the
  paragraph's example now spells "using-declaration" as a grammar term.
  The rule the model cites, overriding by correspondence, is unchanged.
- **Three more cited paragraphs differ on the draft's main, all
  editorially** (24 October 2026). `make drift-check-current` reports
  [class.dtor]/7, [special]/7 and [dcl.init.ref]/5 beside the two known
  before. The first spells "multidimensional" without a hyphen, the
  second indexes "potentially constructed subobjects" with a different
  macro, and the third splits one bullet of the reference-binding rule
  into two, "is either an rvalue (but not a bit-field), or an lvalue of
  function type". No sentence the model cites changes its meaning
  (`decisions.md#draft-pin`).
- **A requirement that fails for every argument is diagnosed** (24
  October 2026). [expr.prim.req.general]/5 ends: if the substitution of
  template arguments into a requirement would always result in a
  substitution failure, the program is ill-formed, no diagnostic
  required. Two emitted cases first wrote `typename S<T, int>;` for an
  `S` of one parameter, a type-requirement no argument can satisfy, and
  GCC 15 and Clang 24 both rejected the translation unit the model
  expected well-formed. The model does not check the condition; the
  cases now fail through a default template argument, `std::enable_if_t`
  on a concept the argument decides, so the failure depends on the
  argument and both compilers agree.
- **A second `std` attribute on a declaration replaced the first** (23
  October 2026). The citation attribute is a Lean parametric attribute,
  which holds one parameter per declaration, so `@[std rule "a", std rule
  "b"]`, two attributes in one list, kept only `b`, with no error. Nine
  declarations of phase 11 and one of phase 9 (`instantiationPoints`,
  whose [temp.point]/1 citation `Decl.refersTo` also carries) had cited
  that way, which is why the citation index listed [over.ics.user]/1,
  [over.best.ics.general]/4 and /6 and [over.match.ctor]/1 as uncovered
  while the code cited them. The parameter is now the list of
  citations, written `@[std rule "a" "b"]`, the index flattens it, and
  the lint counts citations and declarations separately. No citation
  was wrong; some were unrecorded. The comma form still parses, so the
  attribute now refuses a second application on a declaration that
  already carries citations, and the first citation stays; Lean's
  `registerParametricAttributeExt` lets the attribute read its own
  extension before it adds an entry.
- **A class in the fragment has one value, so a conversion identifies
  totally** (23 October 2026). Phase 11 needed the value of the
  candidate initializer `constexpr T v = A;` when the initialization
  goes through a converting constructor or a conversion function, and
  the fragment has no constructor bodies. It does not need them: a
  class value in the model lists its base subobjects and nothing else,
  so every object of a class is template-argument-equivalent to one
  value, `Program.uniqueValue`, whichever constructor made it. That is
  what `Program.candidateInitializer` answers through a user-defined
  sequence, and `conversion_identifies` follows: two values of other
  classes that convert to a class-typed parameter name one
  specialization, whatever they were. Slicing identified a derived value
  with its base; a conversion identifies everything that converts. The
  compilers agree: `constructed_value.cpp` and `converted_value.cpp`
  deduce the constructed object on GCC 15 and Clang 24 alike. GCC, which
  still rejects the sliced derived value (`derived_to_base_value.cpp`),
  accepts the constructed one: a converting constructor is a
  user-defined conversion, which a converted constant expression admits
  under the rule before P2308R1 as well.
- **A value for a placeholder reference parameter was accepted** (23
  October 2026). Phase 10's conversion of a template argument took a
  placeholder's argument as it stood, so `template <const auto &X>` took
  a class value, which in C++ is the invented declaration `const auto &x
  = E;` binding a temporary, forbidden by [temp.arg.nontype]/6. The
  rule was modelled for a declared reference type only. `bindsTemporary`
  now refuses a value for any reference, placeholder or not
  (`placeholder_reference_refuses_value`), and the guard that asserted
  the old answer says the new one. Nothing on the typeclass side
  changed: the pinning routes pass references, and the by-value route's
  placeholder is not a reference. The correction is what makes
  `converted_instance_temporary` true: a converted instance, a prvalue,
  cannot be pinned.
- **A dependent call's meaning is fixed at its first point of
  instantiation** (22 October 2026). [temp.point]/1 puts the point of
  instantiation of a function template specialization after the
  namespace-scope declaration that refers to it, and /7 adds the end of
  the unit; two points with different meanings are ill-formed, no
  diagnostic required. Until now the model read every dependent call
  through the end-of-unit point alone. With the referring declaration in
  the program (`Decl.refersTo`) the draft's own [temp.res.general]/1
  program, read with `h` before `void f(E);`, is the verdict: at the
  point after `h` only `f(char)` is found and the call is not viable, at
  the end `f(E)` is selected (`later_function_verdict`). The model
  resolves the call from the first point, and so do GCC and Clang: the
  emitted referring declaration is an alias of the call's type, which
  the compilers substitute where it stands, so a later overload never
  changes it and a call with no match there is a hard error, one of the
  meanings the verdict allows. For a program with no referring
  declaration the first point is the unit's end, so nothing emitted
  before moves (`pointVerdict_unreferenced`).

- **Narrowing of a constant is representability** (21 October 2026).
  [dcl.init.list]/7 makes an integral conversion narrowing when the
  target type cannot represent every value of the source type, except
  for a constant whose value fits. For a constant source the first half
  adds nothing: a constant's value lies in its own type's range, so when
  the target covers the source the value fits, and narrowing is exactly
  the value not being representable in the target
  (`narrowing_constant`). This is why the model's values need no type of
  their own (`decisions.md#value-typing`): for a constant, the source
  type decides nothing the value does not.

- **The hidden constrained member is a theorem** (20 October 2026). The
  audit found the library's Functor implementations hiding
  `derive_functor`'s constrained `fmap` behind an unconstrained one of
  their own, by member name lookup stopping at the first class whose
  scope declares the name. With [class.member.lookup]/3 in the model
  that is `derived_member_hides_base`, and the shape itself is
  `unconstrained_member_hides_constrained`: a probe of `fmap` through
  the instance resolves over the unconstrained member and the base's
  constraint is never consulted
  (`class_member_lookup_3_hidden_constrained_member.cpp`). The
  "no other lookup on the name" obligation is a theorem too
  (`object_design_candidates`): an object named `fmap` makes its class's
  call operators the whole candidate set, and `call_stability_object` is
  `call_stability` with that hypothesis discharged.

- **A redeclaration was two candidates** (20 October 2026). The candidate
  set of a call was every declaration with the callee's name, so
  `void f(int); void f(int);` gave `f(1)` two candidates with one
  signature, neither better than the other, and the model reported an
  ambiguity between a function and itself
  (`candidates_redeclaration_ambiguous`). The two declarations correspond
  ([basic.scope.scope]/4) and declare one function. The overload set now
  keeps one declaration per entity (`Program.overloadSet`, `entities`),
  resolution over it selects the function, and a redeclaration after the
  entity's first declaration changes no call (`redeclaration_inert`). The
  emitter numbers a redeclaration with its entity, since a redeclaration
  with a different return type is ill-formed C++
  (`basic_scope_scope_4_redeclaration.cpp`). Nothing emitted before had a
  redeclaration, so no earlier expectation moves
  (`overloadSet_eq_candidates`).

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
  and #5, come out as the draft says (`OverloadTest/Lookup.lean`).

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

## About the library

- **The library's members, re-audited** (22 October 2026). The probes
  of 18 October were rerun at beman.transpose `5d248b9`, after the
  fixes for steve-downey/typeclass#10 to #14 and #17 to #20. Every
  member probe answers as required except `kleisli`'s, whose constraint
  still ends `|| true`: the Functor, `std::array` Applicative and
  optional Monad members are constrained on the callable, the derived
  members of Foldable and Monad on the caller's, `invoke` and `map`
  refuse a `void` result, the accumulating object's `bind` is a deleted
  function, and `zip_list`'s and the sender's `invoke` say in their
  constraints that they copy the callable. `lifted_monoid` and
  `kleisli_monoid` hold the typeclass object, so a stateful one is
  consulted. The accurate-members row of [obligations](obligations.md)
  is met at that commit, and the instance-state row with it. Placement
  is unchanged by decision: an instance for a standard type is declared
  with the type, in a header standing in for the standard one, and
  including it is the program's obligation. The umbrella header moved
  up a level, to `beman/transpose.hpp`, and the probes include it
  there. The tables are in [probes](probes.md#library-probes).

- **Applicative's interface is the instance** (17 October 2026). In
  beman.transpose the call a user writes is a member call on the instance
  of record: `const auto &app = applicative<std::optional<int>>;
  app.invoke(f, x, y, z)` (`examples/transpose/apply_example.cpp`). The
  operation object `invoke_fn` is a secondary interface over it, with one
  `operator()` constrained on `TC.invoke(...)`. Functor's `fmap_fn` is the
  same secondary layer, and `encoding.hpp` reduces to it. The theorems
  still apply:
  - The lookup theorems are about the variable template, which a direct
    use names exactly as the operation object does: `coherence`,
    `stability`, `verdicts_single`, `late_insertion_verdict`. A direct use
    in a non-template function has no template argument to carry the
    instance, so it is no better separated across units than the
    operation object (`operation_object_not_separated`).
  - The call-surface theorems apply to `invoke_fn` as to `fmap_fn`. It
    has one `operator()`, keyed at `std::remove_cvref_t` of its first
    in-context argument. Its trailing pack is outside the model's
    fragment, and does not enter the lookup. The key is the first
    argument only, so the instance has to constrain the rest, as
    `optional_applicative_impl` does with `is_optional_v<REST>`.
  - The member call `app.invoke(...)` gets no argument-dependent lookup,
    which applies only to an unqualified name ([basic.lookup.argdep]/1).
    Member lookup stops at the first class whose scope declares the name
    ([class.member.lookup]/3), so `optional_applicative_map`'s
    using-declaration of its implementation's `invoke` hides
    `derive_applicative`'s, and the call has one template.
  - The using-declaration is what lets a member out of the protected
    base. Each member takes `this auto &&`, and the explicit object
    parameter deduces as the instance type. No derived-to-base conversion
    is formed, so `protected_base_selected_ill_formed` is not reached.
  - The derived operations call `self.invoke(...)` with `self` deduced as
    the instance, so they use the most-derived instance's surface, by
    hiding and not by virtual dispatch. Their specializations carry the
    instance type, which separates them as `byValue_separated` does, to
    the extent instance types are distinct.

  What changes is the weight of one hypothesis. The model treats
  `TC.fmap(...)` as an atomic constraint, true when the lookup selects an
  instance. For the primary interface that member overload set is the
  whole call, and getting it right is the job of the derivation base and
  the instance. Two observations against beman.transpose at `30a707d`, on
  GCC 16 and Clang 23 (GCC 13 and Clang 17 lack deducing this):
  - *Re-exposure carries the soft failure.* `derive_applicative::invoke`
    has no constraint and a deduced return type. A probe of it, either
    `requires { app.invoke(f, x); }` or the operation object's constraint,
    instantiates its body to deduce the type. Errors there are not in the
    immediate context ([dcl.spec.auto.general]/15), so the body's
    `static_assert` fires and a call that should not be viable is a hard
    error. Every instance in the library re-exposes its implementation's
    constrained `invoke` with a using-declaration, which hides the derived
    one. An instance without that loses soft failure for `invoke` and for
    `invoke_fn`. (Corrected 18 October 2026: Functor has the same
    problem the other way round. Its implementations' `fmap` is the
    unconstrained member, and the using-declarations hide
    `derive_functor`'s constrained one. See the audit below.)
  - *An `ap`-only basis accepts a function it cannot call.* Where the
    implementation supplies `ap` and no `invoke`, the derived `invoke`
    curries through `terminating_partial`. When the function cannot take
    the arguments, the partial adds the argument to its bound arguments
    and does not fail. `app.invoke(not_callable{}, box<int>{1})`
    compiles and yields a `box` holding an unsaturated partial, and the
    probe reports the call as valid. This is neither a soft failure nor an
    error. It is a wrong answer, and a bug in the library. No instance in
    the library uses an `ap`-only basis, so nothing that ships shows it.

- **The library's members, audited** (18 October 2026). Every typeclass
  in beman.transpose at `30a707d` was probed for the two obligations
  that the model takes as given: that each member an instance exposes is
  accurate, and that each instance is visible wherever its lookup is
  used. The lookups themselves meet every other obligation: the primary
  is `std::false_type` for `functor`, `applicative`,
  `accumulating_applicative`, `monad`, `foldable` and `traversable`. Each
  operation object keys at `std::remove_cvref_t`. No type has two
  instances of one typeclass. Each typeclass has its own instance type,
  and no instance type derives from another. A missing instance fails
  softly through every operation object. The members do not all meet the
  first obligation, and the placement of instances for std types does not
  meet the second. The probes and their table are in
  [probes](probes.md#library-probes).
  - *Re-exposure is only as good as what it exposes.* The optional and
    vector Functor implementations' `fmap` is unconstrained with a
    deduced return type, and the instances' using-declarations hide
    `derive_functor`'s constrained `fmap`. A call with a function the
    element cannot be passed to is a hard error. The `std::array`
    Applicative implementation constrains `invoke` on shape alone, with
    the same result. Whichever member lookup finds has to be accurate.
    Hiding the derived member is right only when the implementation's
    member is the more accurate of the two.
  - *Derived members whose constraint is weaker than their body.*
    `invoke_with`, `bind_with`, `for_each` and `traverse_with` are
    unconstrained. `derive_monad::invoke`, `fold_left`, `fold_right` and
    `find_first` have a disjunct that passes where the body then fails.
    All are hard errors on a probe. `any_of` and `all_of` are worse: the
    probe says the call is valid, and the call is a hard error.
    `kleisli`'s constraint ends `|| true`, which moves the error to the
    call of the composed function.
  - *A non-monadic function is accepted by `bind`.* `OptionalMonadImpl::
    bind` returns whatever the function returns, value-initialized for
    the empty case. `bind(std::optional<int>{}, inc)` is `0`, an `int`,
    and `join(std::optional<int>{1})` compiles through it. That is a type
    error the library accepts, not an overload hazard. The probe of the
    call is accurate about the member, and the member is wrong.
  - *Instances for std types away from their typeclass.*
    `applicative<std::array>` is in `array.hpp`. The `std::expected`
    instances are in `expected.hpp`, `applicative<std::simd::basic_vec>`
    in `simd.hpp`, and `foldable` and `traversable` for `std::vector` in
    `sequence.hpp`. None of these is the header of the typeclass or of
    the type. A use of the lookup before the instance's header is
    included, in a unit that includes it later or alongside a unit that
    includes it, is ill-formed with no diagnostic required
    ([temp.spec.partial.general]/1). This is the verdict
    `late_insertion_verdict` predicts, reached through shipped headers.
    GCC 16 diagnoses the late partial specialization. Clang 23 keeps the
    first answer: after `array.hpp` is included, `invoke` on a
    `std::array` still finds no instance. The instances for library types
    (`zip_list`, `sender`, `simd_lanes`) sit in the type's own header,
    which every use of the type has to include, so they are safe.
  - *Monoid is a third encoding.* `Monoid<V>` is a class template
    declared and never defined. An instance is a specialization of it,
    and `detail::has_registered_monoid` tests for one by completeness,
    `requires { Monoid<V>{}; }`. The variable `monoid<V>` is a hard
    error for a type without one, so the soft-primary obligation fails
    for it. Every use in the folds goes through the concept first, so
    nothing reaches the hard error. The concept's answer for a type
    changes when a specialization is declared, which is ill-formed with
    no diagnostic required by a third rule, a satisfaction result that
    differs at two points ([temp.constr.atomic]/3). It is the same hazard
    under a different citation.
  - *Two `operator()`s in one operation object.* `fold_map_fn` and
    `combine_all_fn` each have two, one taking an explicit monoid and one
    taking none. They differ by arity, and the lookup default comes after
    the parameter that the shorter call cannot deduce. A call of one
    arity therefore fails deduction in the other before that one reaches
    the lookup. The operation object is no longer a single candidate, but
    no candidate the call does not mean consults the lookup.

  The model now states the member call's answer as a parameter, and
  proves that the operation object passes it on unchanged
  (`fmapObject_member`). The arity and registry shapes are theorems too
  (`call_stability_arity`, `arity_order_matters`, `registry_verdicts`).
  The order of the lookup default matters only beside an `operator()`
  that does not consult the lookup. `fold_map` and `combine_all` key both
  overloads at the same type, so for them either order gives the same
  outcome.

  Reported as steve-downey/typeclass#10 (Functor impls), #11 (`std::array`
  impl), #12 (derived members), #13 (`bind`) and #14 (placement). A
  correction to #6 is posted on it.
- **What an algorithm can rely on** (18 October 2026). An algorithm that
  takes an instance relies on more than the concept checks. The algorithm
  probes (`probes.md`) size each gap, and
  [plan.md](plan.md#algorithm-author-obligations) weighs them.
  - *The witness is a good proxy, except for copies.* Each concept checks
    its members with one fixed callable. Of 88 member and callable pairs,
    85 behave as the witness predicts. The three that do not are all the
    callable being copied. `zip_list`'s `invoke` runs a copy of a stateful
    lvalue callable, so the caller's object never sees the calls, which is
    silent. The sender's `invoke` says a move-only lvalue is valid, and
    the call then fails.
  - *A second instance is reachable by accident.* Under the accumulating
    object, an algorithm that slips once to `bt::invoke` or `bt::bind`
    keeps the first error and drops the rest, and compiles. The library's
    own derived members and `traverse` use the object they are given.
  - *Asking is sometimes an error.* `monad_object` of the accumulating
    object is a hard error, because its refused `bind` is a
    `static_assert` in a deduced body.
  - *Fresh instances drop state.* `lifted_monoid` and `kleisli_monoid`
    make their own applicative or monad object, so a stateful one passed
    by type is never consulted. Every registered typeclass object is
    empty, so nothing in the library is affected.

  None of these changes the value a computation returns. The silent ones
  lose a callable's state, an object's state, or error evidence.
  Coherence between two instances for one context is beyond the model,
  which has one instance per key. What the model does prove is the
  algorithm's side of accuracy. An algorithm whose constraint is the
  conjunction of its member calls answers as they do, in the order
  written (`algorithm_transfer`), and is accurate when they are
  (`algorithm_accurate`). A guard written after the call it protects
  protects nothing (`call_order_matters`).

  Reported as steve-downey/typeclass#17 (callable copies), #18 (`void`
  results), #19 (the accumulating `bind`) and #20 (`lifted_monoid` and
  `kleisli_monoid`).

- **The value route is closed to the library's instance types** (21
  October 2026). `derive_functor<Impl>` keeps `Impl` as a protected
  base, so neither it nor an instance type derived from it is a
  structural type ([temp.param]/12), and a class value of such a type is
  not permitted for a placeholder constant parameter
  ([temp.arg.nontype]/1; `value_route_needs_structural`). The plan's
  value route cannot take the library's instances by value, whatever its
  identity properties. With its parameter typed at a base it would slice
  a derived instance to the base (`value_route_slices`), which is leak 4
  as a theorem; the reference parameters the library uses keep the
  object's identity (`pin_keeps_identity`).

## Design note

- **A variable cannot be overloaded** (17 October 2026). The typeclass
  design in beman.transpose puts a variable at each point where C++ would
  otherwise build an overload set, and most of its good behaviour follows
  from that.
  - The operation object. `fmap` is a variable, so name lookup for
    `fmap(f, x)` finds one entity, and the call has one candidate, its
    `operator()`. Argument-dependent lookup does not run when ordinary
    lookup finds an object, and nobody can add an overload that competes
    with it or consults the lookup. That is the "no other lookup on the
    name" hypothesis of `call_stability`, met by construction.
  - The instance. `functor<T>` is a variable template, and choosing an
    instance is partial specialization matching, not overload resolution.
    Conversion ranking, argument-dependent lookup and the non-template
    preference never touch it. Coherence and stability are theorems about
    matching alone (`coherence`, `stability`), and no ranking can change
    the instance a call selects (`separability`).
  - The members. With an instance in hand, `TC.fmap(...)` is member
    lookup in one class, which nothing at namespace scope can join. This
    is the primary interface. A user writes `app.invoke(...)` on the
    instance of record, and the operation objects are a layer over it
    ([applicative](#about-the-library)).

  The trouble the model found is where an overload set comes back: route
  overloads beside the canonical `operator()` (`routes_type_ambiguous_hard`,
  `routes_argument_default_ambiguous`), priority tags, which check every
  overload's condition (`dispatch_hard_condition`), a function that names
  an instance type (`rank_beats_refinement`, `derived_class_deduction`,
  `protected_base_selected_ill_formed`), and the instance's own members,
  such as `derive_functor`'s constrained `fmap` and `replace`, an overload
  set its author owns. It is accurate only where its author made it so:
  the audit found members on every typeclass that are not.

  The one hazard runs the other way. Because the operation object names
  the lookup variable, which is one entity in every translation unit, two
  units that select different instances give one specialization two
  meanings, ill-formed with no diagnostic required
  (`operation_object_not_separated`). Being a variable is what makes it
  immune to overloading, and what exposes it to the one-definition rule.
