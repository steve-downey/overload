# Obligations

This is the obligations table that [the plan](plan.md#proof-obligations) calls for,
as harvested so far. Each row is a hypothesis that a proved theorem needs
and the language does not guarantee. The plan's table holds the
predictions. This one says what the model found, and where the
prediction failed. The classes are the plan's: by construction,
compiler-checked, library-checkable, undiagnosable.

Rows wait for their theorems. Superclass coherence and visible
refinement need inheritance erasure, superclass coherence and
sfinae-requires. Exact-type use has its counterexample but not yet the
theorem it supports. Instance in the
signature needs divergence-separation, phase 8.

## Harvested

| Obligation | Owed by | Needed for | Discharge found | Prediction |
|---|---|---|---|---|
| Canonicity: no two instances match a type with neither more specialized. | Instance author | `coherence`, `call_stability` | Compiler-checked under the text: an ambiguous lookup is ill-formed, at the lookup and at every call that substitutes it. The compilers diagnose the lookup itself (`instance_ambiguous`). At the call surface they do not: GCC 13 to 16 and Clang 17 to 24 treat the ambiguity as a deduction failure, and the type looks as if it had no instance ([findings](findings.md#compiler-disagreements)). | Held for the text. Failed for the compilers. |
| Soft primary: the lookup's primary is a value, `std::false_type`, not a hard error. | Typeclass author | `call_stability`, `fmapObject_outcome`, `byValue_omitted_outcome` | By construction in the library: the primary is `std::false_type`. | Held. |
| Soft failure: a missing instance makes the call not viable. | Typeclass author, or the author of a pinning function | `call_stability` | By construction for the operation object, whose constraint is the call through the instance (`fmapObject_outcome`). Library-checkable for the by-value route, through the shapeless default (`byValue_omitted_outcome`). Not discharged for the pinning pattern, which has no constraint: the call is viable and the error is in the body (`unpinned_deduce`). | Held for the operation object. Failed for pinning, where the obligation moves to the user. |
| Shapeless default: `std::false_type` has no instance's shape. | Typeclass author | `byValue_omitted_outcome` | Library-checkable: one `static_assert` per typeclass. | Held. |
| Normalized lookup key: cv and reference qualifiers are removed before lookup. | Typeclass author | `fmapObject_outcome`, `unpinned_deduce` | By construction: the operation object looks up at `std::remove_cvref_t<T>`, and a `const C &` parameter deduces `C` without them (`op_object_normalized_key`). | Held. |
| No other lookup on the name: the other candidates of a call do not consult the lookup. | Typeclass author | `call_stability` | By construction for the library: an operation object has one `operator()` and cannot be overloaded. A design with route overloads must meet it per overload. | Not predicted. |
| Placement: in an overload set of routes, a call meant for an explicit route never substitutes the canonical overload's default. | Typeclass author, for a design with route overloads | the routes as alternatives | By construction for the value and argument routes, which fail the canonical overload on kind or arity first. Not met by the type route (`routes_type_ambiguous_hard`). The library has no route overloads, so it owes nothing. | Not predicted. |
| Instance identity: two uses with different instances are different specializations. | Typeclass author | instance in the type | By construction for pinning: a reference argument is the object it designates ([temp.type]/2). By construction for the type route, and for the value route up to value equivalence, which for empty instances is the type. Not for the by-value route once an instance has state, since only its type enters the specialization. The library passes stateful monoids by value. | Held for the template-parameter routes. The plan's structural-identity row assumed value parameters; the library uses references. |
| Genuine instance: an object passed as an instance is meant as one. | User of explicit instances | `pinned_deduce`, `byValue_passed` | Library-checkable for shape on the by-value, value and type routes. Not checked for pinning, which has no constraint. Intent is convention on every route. | Held, except pinning checks no shape. |
| Visibility and stable satisfaction: every instance is declared before any use, the same in every translation unit. | Instance author, everyone | `call_stability` | Undiagnosable. Not a hypothesis of any theorem yet: the model's environment consults every instance the program declares, wherever the call is, so the single translation unit assumption is built in ([single-tu](decisions.md#single-tu)). | Pending phase 8. |
| Exact-type use: no signature names an instance type concretely, so every use takes an instance at its deduced exact type. | Author of an overload on instances, user of the library | inheritance erasure (owed); `rank_beats_refinement` shows the failure | Undiagnosable as a rule. Each overload is well-formed, and the call moves to the less refined overload without a diagnostic once one instance type derives from another (`leak_rank_derived`). | Held: leak 1 is live, as predicted. |
| Decreasing requirements. | Instance author | termination | Vacuous for the library: no instance requires another. | Not needed today. |
