# Probes

Three hand-written C++ probes, run on GCC 13.3 and Clang 18.1 with
`-std=c++23`, before any Lean existed. Two produced compiler disagreements
and one produced the counterexample the step-order suspect predicted. The
sources are in `probes/`, and `make probes` (or `probes/run.sh g++-13
clang++-18`) reruns them and prints the table.

The sources here are reconstructions from the plan's descriptions; the
originals did not come with the plan. A reconstruction is accepted when it
reproduces the plan's results table on the same compiler versions. Two cells
did not reproduce at first and one still does not; both are recorded below.

## Step-order probe

A candidate with a defaulted constant template parameter whose default
performs an instance lookup, where the lookup fails with a `static_assert`
for the argument type, alongside a second candidate that should win.

| Variant | Winning candidate | GCC | Clang |
|---|---|---|---|
| A | non-template, exact match | compiles | hard error |
| B | as A, but the primary template is declared and never defined | compiles | compiles |
| C | as A, with a requires-clause on the template guarding the lookup | compiles | hard error |
| D | as A, soft design: `std::false_type` default, constrained on instance shape | compiles | compiles |
| E | as A, lookup moved into a default function argument | compiles | compiles |
| G | non-template, worse match, so the template competes | hard error | hard error |
| H | as A, lookup in the return type instead of the default argument | compiles | hard error |
| I | a more specialized template, exact match | hard error | hard error |

Reproduced in full by `probes/step_order.cpp` on 15 October 2026.

Findings:

- **The hazard is real on both compilers.** Variant I is the counterexample:
  a template candidate that loses on partial ordering still has its default
  substituted, and the hard error poisons the call. Variant C confirms that
  a requires-clause on the same template cannot guard the default, because
  the default is substituted first.
- **GCC and Clang disagree when a non-template exact match exists.** Variants
  A, C and H compile on GCC and fail on Clang. GCC appears not to perform
  deduction for template candidates at all when a non-template candidate is
  a perfect match. The draft example in [temp.constr.atomic]/3 supports
  Clang. Filed under test-oracle; the question is whether GCC's shortcut is
  conforming, and the verdict below says it is not, under the C++26 text.
- **The library's design is safe.** Variant D compiles and selects correctly
  on both, which is what missing-instance predicted.
- **Two further soft routes.** An undefined primary template (B) is treated
  as a substitution failure by both, and a default function argument (E) is
  not instantiated unless the candidate is selected. E is relevant to the
  by-value explicit-instance route.
- **The soft route of B depends on the spelling of the lookup**
  (reconstruction finding, 15 October 2026). B reproduces when the default
  names the class template's static member directly,
  `functor_instance<T>::value`: an undefined primary used there is an
  invalid expression in the immediate context. Routed through a variable
  template, `functor<T>` whose initializer is `functor_instance<T>::value`,
  the same undefined primary is a hard error on Clang, because the variable
  template specialization is a separate instantiation and its failure is
  outside the immediate context ([temp.deduct.general]/8 sentence 4).
  `probes/step_order_variable.cpp` keeps that variant. The modelled library
  looks up through a variable template, so for it only D and E are soft
  routes.

## Tie-break probe

Two overloads where the second is more constrained, varying how the
instance bound is written.

| Variant | Difference between overloads | GCC | Clang |
|---|---|---|---|
| A | requires-clauses only | #2 wins | #2 wins |
| B | #2 has an extra defaulted template parameter | ambiguous | ambiguous |
| C | bound as a type-constraint on an `auto` constant parameter | ambiguous | #2 wins |
| D | constant parameters of different concrete instance types | ambiguous | ambiguous |

`probes/tie_break.cpp` reproduces A, B and D. Variant C does not reproduce:
with the bound spelled `shape auto TC` by value, both compilers report
ambiguity, and spelled `const shape auto& TC` Clang 18.1 rejects the
declaration outright ("constrained placeholder types other than simple
`auto` on non-type template parameters not supported yet"). The plan's
Clang result for C needs the original source; until it is found, C is
recorded as not reproduced and the verdict below stands on the text alone.
The model's own emission of C, `tie_break_placeholder_constraint.cpp`,
computes #2 and both compilers answer ambiguous (`findings.md`).

Findings:

- **B and D confirm the suspect.** A difference in parameter list length or
  in constant parameter type switches the tie-break off, and the more
  constrained overload loses to ambiguity.
- **C is a compiler disagreement.** [temp.over.link]/6 says equivalence of
  constant parameters ignores type-constraints on placeholder types, which
  makes the parameters equivalent and the tie-break apply, so Clang matches
  the working draft. GCC 13 does not implement it either way.

## Constant-argument conversion probe

A derived-class value supplied for a base-typed class-type constant
template parameter.

| Variant | Question | GCC | Clang |
|---|---|---|---|
| A | is the derived value accepted, with slicing | rejected: not a converted constant expression | accepted |
| B | is the sliced argument the same specialization as the base value | rejected | same specialization |

Reproduced in full by `probes/constant_conversion.cpp`.

Findings:

- **A third compiler disagreement.** Clang accepts the derived value, slices
  it, and identifies the result with the equivalent base value. GCC rejects
  it as a conversion not permitted in a converted constant expression.
- **If Clang is right**, leak 4 under instance inheritance is live: a derived
  instance passed as a literal template argument silently becomes its base.

The disagreements are what the test-oracle decision anticipated: each is
filed against a sentence, not settled by majority, and MSVC and EDG should
be consulted through Compiler Explorer on all three.

## Who is right, 15 October 2026

Checked against the C++26 text at eel.is and the draft repository's
history.

| Divergence | Governing text | Verdict | Action |
|---|---|---|---|
| 1. Default argument substituted for a losing template candidate | [over.match.funcs.general]/8: candidate specializations are generated by deduction for each function template, with no exception for a non-template exact match | Clang follows the text. GCC's shortcut is the subject of P3606, polled with consensus in EWG in March 2025, forwarded to CWG for C++29 with weak consensus at Kona, and returned by CWG in June 2026 needing updates; R2 was posted in September 2026 | No report. Watch P3606. The model transcribes the text, and gains a switch for the P3606 behaviour once its wording settles (decisions.md#p3606-mode) |
| 2. Constrained `auto` constant parameter and the tie-break | [temp.over.link]/6.3, introduced by P2113R0 in February 2020 and so C++20 text | Clang is correct. GCC implements P2113 for type parameters, per its test concepts-p2113a.C, but applies no carve-out for type-constraints on placeholder types | GCC bug report, after checking trunk |
| 3. Derived value for a base-typed class constant parameter | [temp.arg.nontype]/1 and /3 as rewritten by P2308R1 in November 2023: for class type T the argument must make `constexpr T v = A;` valid, and the paper states that no restrictions are imposed on the conversion to the constructor parameter. The converted-constant-expression rule now applies only to non-class types | Clang is correct under C++26. GCC's diagnostic applies the pre-P2308 rule, which was the C++20 and C++23 text | GCC bug report, after checking trunk. Whether P2308R1 applies as a defect report to earlier modes is a question for the report |

Consequence for the model: leak 4 under instance inheritance is live under
C++26. A derived instance supplied as a literal template argument for a
base-typed constant parameter is sliced and identified with the base value.
The obligation that instances are taken at their deduced exact type now
covers constant parameters as well as function parameters.

## Library probes

The probes in `probes/library/` check beman.transpose itself, not the
model's reductions. Each line of `probes.txt` asks whether one call into the
library is a valid expression. It is compiled as its own translation unit and
classified as soft (not a valid expression, the clean answer), valid, or
hard (checking the call is itself an error). `make probes-library
BEMAN_TRANSPOSE_INCLUDE=dir` reruns them. The library needs deducing this:
GCC 14 and Clang 19 are the oldest that compile it here, and Clang 18
crashes on it.

They test two obligations from [obligations](obligations.md#harvested):
that every member an instance exposes is accurate, and that an instance is
visible wherever its lookup is used. The findings are in
[findings](findings.md#about-the-library).

Recorded at beman.transpose `30a707d`, GCC 16 and Clang 23. Both compilers
give the same answer on every row, so one column is shown. Every probe not
listed is soft, as required, and the three controls are valid.

| Probe | Required | Observed | Cause |
|---|---|---|---|
| `fmap(not_callable, optional)`, and the member call | soft | hard | The optional and vector Functor impls' `fmap` is unconstrained with a deduced return type, and the instances' using-declarations hide `derive_functor`'s constrained `fmap` |
| `invoke(not_callable, array)` | soft | hard | `array_applicative_impl::invoke` is constrained on shape only |
| `applicative<optional>.invoke_with(…, not_callable, …)` | soft | hard | unconstrained derived member |
| `bind(optional, inc)` | soft | valid | `OptionalMonadImpl::bind` does not require the function to return an optional; the call returns `int` |
| `join(optional<int>)` | soft | valid | through the same `bind` |
| `kleisli<optional>(not_callable, not_callable)`, and the member call | soft | valid | `requires … \|\| true`; the error moves to the composed function's call |
| `monad<optional>.bind_with(…, not_callable)` | soft | hard | unconstrained derived member |
| `monad<optional>.invoke(not_callable, …)` | soft | hard | derived member whose constraint is weaker than its body |
| `fold_left`, `fold_right`, `find_first` with `not_callable`, and the member `fold_left` | soft | hard | the second disjunct of the constraint passes and the body fails |
| `any_of`, `all_of` with `not_callable` | soft | valid | the constraint passes; the call is then a hard error |
| `traversable<vector>.for_each`, both `traverse_with` | soft | hard | unconstrained derived members |

`late_array.cpp` uses the `std::array` instance before and after
`array.hpp` is included.

| Variant | GCC 16 | Clang 23 |
|---|---|---|
| P: probe before the include only | error: partial specialization after instantiation | compiles |
| A: also assert the instance is visible after it | error | error: the stale answer stands |
| C: call through it after it | error | error: no matching function |

Both are conforming. The program is ill-formed with no diagnostic required
([temp.spec.partial.general]/1). GCC diagnoses it, and Clang keeps the first
answer.

Reported upstream as steve-downey/typeclass#6, #7, #10 to #14.

## Algorithm probes

These ask what an algorithm written against a typeclass can rely on when it
is handed an instance. `parametricity.txt` asks whether each member that
accepts the concept's witness accepts the callables a user would pass.
`algorithms.txt` asks which objects satisfy which concepts. Three runtime
probes print what the library does with a second instance for one context
(`coherence.cpp`), with instance state (`state.cpp`) and with a stateful
callable (`callable_state.cpp`). `make probes-library` runs them all.

Recorded at beman.transpose `30a707d`, GCC 16 and Clang 23, on 18 October
2026. The compilers agree on every row.

Parametricity covers ten members: `invoke` on the optional, expected,
accumulating expected, array, `zip_list` and sender objects, optional
`map`, optional and vector `fmap`, and vector `any_of`. Each gets seven
callables a member should accept: by value, by `const&`, generic, function
pointer, move-only as an rvalue and as an lvalue, and a non-`const` call
operator as an lvalue. Optional `bind`, the vector `traverse` member and
the `traverse` operation object get six monadic ones. Of the 88 cells, 85
are valid and the call compiles when it is made. The other three all come
from the member copying the callable. The `void`-result, `int&&` and
non-callable rows were run alongside them.

| Probe | Required | Observed | Cause |
|---|---|---|---|
| `zip_list` `invoke`, move-only lvalue | valid | hard | the body copies the callable into a local; the return type is deduced |
| sender `invoke`, move-only lvalue | valid | valid, and the call does not compile | the trailing return type asks only `invoke_result`; the body copies the callable into the deferred lambda |
| sender `invoke`, non-`const` call operator | valid | soft | the deferred lambda calls the stored copy as `const`; the trailing return type says so |
| optional, array, `zip_list`, sender `invoke` and optional `map`, `void` result | soft | hard | `std::optional<void>` or the context's equivalent is named outside the immediate context |
| optional and vector `fmap`, `int&&` parameter | any | hard | the unconstrained impl `fmap` (#10) |
| vector `any_of`, `void` predicate | soft | valid | the constraint passes and the body fails (#12) |

`std::expected<void, E>` is a type, so a `void` result there is valid and
correct. Every other row not listed answers as required.

| Probe (`algorithms.txt` and the capability rows) | Required | Observed |
|---|---|---|
| `monad_object` of the accumulating object | soft | hard: its `bind` is a `static_assert` in a deduced body |
| `accumulating_applicative<E>.bind(…)` | soft | hard, the same |
| `applicative_object` of the accumulating object | valid | valid |
| `monad_object` of `applicative<optional>`, of `applicative<expected>` | either | soft |
| `applicative_object` of `monad<optional>`, of `monad<expected>` | either | soft |
| `traverse` with `monad<optional>` or `monad<expected>` as policy | either | soft |
| `applicative<optional>.collect(…)` | soft | soft |
| `fmap(not_callable, …)` through a `const derive_functor<…>&` | soft | hard, as through the instance: the base's constraint asks the impl |

No registered object is both an applicative object and a monad object, so
a monad object cannot be passed where an applicative object is asked for.

`coherence.cpp`, two failing operands under the accumulating object, at
`std::expected<int, error_set<alpha, beta>>`:

| Computation | alpha | beta |
|---|---|---|
| `acc.invoke(plus, a, b)` | kept | kept |
| `bt::invoke(plus, a, b)` in an algorithm given `acc` | kept | lost |
| `bt::bind` in an algorithm given `acc` | kept | lost |
| `acc.zip_with`, `discard_first`, `discard_second`, `invoke_with` | kept | kept |
| `traverse(f, v, acc)` | kept | kept |
| `traverse(f, v)` | kept | lost, as documented |

`state.cpp`: every registered applicative, monad, functor, foldable and
traversable object, `Monoid<std::string>` and `sum_monoid<int>` is empty
and default-initializable. `lifted_monoid<…, sum_monoid<int>>` is not
empty, since it holds its element monoid. A stateful applicative object
used through `lifted_monoid` is never consulted: `lifted_monoid` makes a
fresh one with `APPLICATIVE_OBJECT{}`, and the type gives no way to pass
one in. The sum is right and none of the object's calls are logged.

`callable_state.cpp`: a stateful callable passed as an lvalue keeps its
count through every member probed except `zip_list`'s `invoke`, which runs
a copy. The caller's object sees no calls. `std::ref(f)` gives the right
count, and `std::cref` lets the sender take a move-only callable.

Rerun at beman.transpose `9014608`, GCC 16 and Clang 23, on 18 October
2026. Every algorithm probe answers as above, and the sender's move-only
lvalue call still fails. In the library probes, `invoke_with`,
`bind_with`, `for_each` and both `traverse_with` rows now answer soft, as
required, after PRs #9, #15 and #16. Every other library probe answers as
recorded at `30a707d`.

Reported upstream as steve-downey/typeclass#17 to #20.
