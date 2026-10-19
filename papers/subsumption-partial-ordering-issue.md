# Subsumption is a preorder, not a partial ordering

Draft of an issue against [temp.constr.order]/2, in three forms, in the
order they would be tried: a brief post on the Core Mattermost channel, to
find out whether the editor will take it as editorial; an editorial issue
for the cplusplus/draft tracker; and a Core issue in the CWG format should
it be judged a change in meaning. The finding is recorded in
[findings.md](../docs/findings.md#against-the-standard); the proof is
`Constraint.subsumes_not_antisymm` in `Overload/Constraint.lean`.

## Mattermost post

> Small one in [temp.constr.order]/2
> (<https://eel.is/c++draft/temp.constr.order#2>). Note 1 says "The
> subsumption relation defines a partial ordering on constraints"
> (<https://eel.is/c++draft/temp.constr.order#2.sentence-1>). It is a
> preorder, not a partial ordering: by the definition in /1
> (<https://eel.is/c++draft/temp.constr.order#1>), `A && B` and `B && A`
> subsume each other and are different constraints, so it is not
> antisymmetric. Nothing normative depends on it, since /4 and /5
> (<https://eel.is/c++draft/temp.constr.order#4>,
> <https://eel.is/c++draft/temp.constr.order#5>) compare both directions
> and get a strict partial order on declarations out of it. Would the
> editor take a fix to the note as editorial, or does this want an issue?

The sentence anchor is spelled as eel.is renders it and as the model's
citations use it, `#2.sentence-1`.

## The text

[temp.constr.order]/2 of N5054 reads, in a note:

> [*Note 1*: The subsumption relation defines a partial ordering on
> constraints. This partial ordering is used to determine
>
> - the best viable candidate of non-template functions ([over.match.best]),
> - the address of a non-template function ([over.over]),
> - the matching of template template arguments ([temp.arg.template]),
> - the partial ordering of class template specializations
>   ([temp.spec.partial.order]), and
> - the partial ordering of function templates ([temp.func.order]).
>
> — *end note*]

## The problem

A partial ordering is reflexive, transitive and antisymmetric. Subsumption
as defined in [temp.constr.order]/1 is reflexive and transitive, but not
antisymmetric. For atomic constraints `A` and `B`, the constraints `A ∧ B`
and `B ∧ A` each subsume the other: the disjunctive normal form of each is
the single clause `{A, B}`, the conjunctive normal form of each is the two
clauses `{A}` and `{B}`, and the one disjunctive clause subsumes both
conjunctive clauses on either side. They are nevertheless different
constraints, with different normal forms as sequences, and the Standard
nowhere identifies constraints that subsume each other. So the relation is
a preorder.

Nothing normative depends on the misstatement. Every normative use of
subsumption asks whether one constraint subsumes another and whether the
converse fails ([temp.constr.order]/4 and /5, "at least as constrained"
and "more constrained"), which is how a preorder is turned into a strict
partial order on declarations. "More constrained" is irreflexive,
asymmetric and transitive as a consequence. Implementations agree with one
another and with the text on every case tested. The note is simply false
as worded, and a reader who takes "partial ordering" at its mathematical
meaning will look for an antisymmetry that is not there.

The claim and its refutation are mechanized. In a Lean 4 model of
[temp.constr.order]/1 over atomic constraints with identity as in
[temp.constr.atomic]/2, subsumption is proved equivalent to propositional
implication with the atomic constraints as free variables, hence reflexive
and transitive, and the pair above is a checked counterexample to
antisymmetry.

## Editorial issue

For github.com/cplusplus/draft, title "[temp.constr.order] Subsumption is
a preorder, not a partial ordering".

The note in [temp.constr.order]/2 says "The subsumption relation defines a
partial ordering on constraints." It does not: `A ∧ B` and `B ∧ A` subsume
each other and are distinct constraints, so the relation is not
antisymmetric. It is a preorder, and it induces the partial orderings the
note goes on to list through "at least as constrained" and "more
constrained" in /4 and /5. Since the sentence is in a note and no normative
text depends on it, this is proposed as editorial.

Suggested change:

> [*Note 1*: The subsumption relation is a preorder on constraints: it is
> reflexive and transitive, but two different constraints can subsume each
> other. ~~This partial ordering~~ The ordering of declarations it induces
> ([temp.constr.order]/4 and /5) is used to determine
>
> - the best viable candidate of non-template functions ([over.match.best]),
> - ...
>
> — *end note*]

A shorter alternative, if "preorder" is thought too much for a note, is to
replace "defines a partial ordering on constraints" with "is used to order
declarations", and leave the list as it is.

## Core issue

If the editor considers the change to be a change in meaning rather than a
correction of wording, the same text as a Core issue.

**Section:** [temp.constr.order]

**Status:** new

**Submitter:** Steve Downey

**Issue:**

[temp.constr.order]/2 states, in Note 1, that "The subsumption relation
defines a partial ordering on constraints." The relation defined in
paragraph 1 is not antisymmetric: for atomic constraints `A` and `B`, the
constraints `A ∧ B` and `B ∧ A` subsume one another and are distinct
constraints. The relation is therefore a preorder. The normative uses of
subsumption, in paragraphs 4 and 5 and in the sections the note lists,
each compare two declarations in both directions and so define a strict
partial ordering on declarations; none depends on antisymmetry of
subsumption itself. The note is nevertheless incorrect as worded, and a
reader who relies on it could expect that mutually subsuming constraints
are the same constraint, which the Standard does not say and which
implementations do not implement.

The relation has been mechanized as a decision procedure over the normal
forms of paragraph 1 and proved reflexive and transitive, with the pair
above as a counterexample to antisymmetry.

**Proposed resolution:**

Change [temp.constr.order]/2 as follows:

> [*Note 1*: The subsumption relation ~~defines a partial ordering on
> constraints. This partial ordering~~ is a preorder on constraints:
> reflexive and transitive, but two different constraints can subsume each
> other. The ordering of declarations it induces ([temp.constr.order]/4
> and /5) is used to determine
>
> - the best viable candidate of non-template functions ([over.match.best]),
> - the address of a non-template function ([over.over]),
> - the matching of template template arguments ([temp.arg.template]),
> - the partial ordering of class template specializations
>   ([temp.spec.partial.order]), and
> - the partial ordering of function templates ([temp.func.order]).
>
> — *end note*]

## Why it is worth filing

The misstatement does no operational harm, and the issue should say so,
to be filed at the right weight. It is worth a correction for two reasons.
A note is where a reader goes to learn what the normative text amounts to,
and this one teaches a property the relation does not have. And "partial
ordering" is a term the same section uses normatively for declarations
([temp.func.order], [temp.spec.partial.order]), where it is a strict
partial order, so the note's use of the same words for a different and
weaker relation on a different set invites exactly the confusion it is
meant to prevent.
