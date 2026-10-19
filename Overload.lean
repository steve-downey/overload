-- Overload.lean                                                      -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Std
import Overload.Syntax
import Overload.Outcome
import Overload.Deduction
import Overload.Generality
import Overload.Constraint
import Overload.Program
import Overload.Steps
import Overload.Ordering
import Overload.Transitivity
import Overload.Specs
import Overload.Resolution
import Overload.Ranking
import Overload.Lookup
import Overload.Environment
import Overload.Separability
import Overload.Erasure
import Overload.Mandates
import Overload.Sfinae
import Overload.Dispatch
import Overload.Units
import Overload.Access
import Overload.Conjunction
import Overload.Emit
import Overload.Typeclass
import Overload.Lint

/-!
# Modelling C++ overload resolution in Lean

The root module imports every module of the model and runs the lints over
all of them, so `lake build` fails when a rule is uncited, an axiom
untagged, or a module of the Standard side imports the typeclass side.
The headline theorems are audited here, the Standard side's first and the
encoding's after them.

The model has two sides. `Overload.*` transcribes the Standard: deduction,
substitution, constraints, partial ordering, variable template lookup,
overload resolution, Mandates, translation units, and the theorems about
them. `Overload.Typeclass.*` defines the typeclass encoding of
beman.transpose on top of that and proves its properties. `docs/guide.md`
is the map.
-/

#check_citations
#check_layering

/-! ## The Standard side -/

-- Deduction and substitution.
#audit Overload.deduceTy_iff
#audit Overload.deduceTy_det
#audit Overload.deduceTy_subst
#audit Overload.deduceTy_most_general
#audit Overload.Val.equivalent_iff
#audit Overload.defaults_hard_absorbing
#audit Overload.constraint_cannot_guard_default
#audit Overload.constraint_soft_shields_function_type
#audit Overload.deduceTemplate_hard_iff
#audit Overload.deduceTemplate_congr

-- Constraints and subsumption.
#audit Overload.Constraint.subsumes_iff
#audit Overload.Constraint.subsumes_refl
#audit Overload.Constraint.subsumes_trans
#audit Overload.Constraint.atLeastAsConstrained_trans
#audit Overload.Constraint.subsumes_satisfied
#audit Overload.Constraint.satisfaction_implication_not_subsumes
#audit Overload.Constraint.subsumes_satisfied_hard
#audit Overload.Constraint.subsumes_example
#audit Overload.Constraint.subsumes_not_antisymm
#audit Overload.Constraint.moreConstrained_asymm
#audit Overload.Constraint.moreConstrained_trans
#audit Overload.satisfied_conjunctionOf
#audit Overload.conjunction_answers
#audit Overload.conjunction_no_hard

-- Partial ordering and partial specialization matching.
#audit Overload.PartialOrdering.moreSpecialized_irrefl
#audit Overload.PartialOrdering.moreSpecialized_asymm
#audit Overload.PartialOrdering.moreSpecialized_trans
#audit Overload.PartialOrdering.moreSpecialized_trans_of
#audit Overload.PartialOrdering.atLeastAsSpecialized_trans
#audit Overload.PartialOrdering.tieBreakApplies_trans
#audit Overload.PartialOrdering.tieBreak_needs_equal_heads
#audit Overload.PartialOrdering.patternMatches_iff
#audit Overload.PartialOrdering.select_iff
#audit Overload.PartialOrdering.mostSpecialized_unique
#audit Overload.PartialOrdering.deduceAll_go_iff
#audit Overload.PartialOrdering.atLeastAsSpecialized_iff
#audit Overload.PartialOrdering.moreSpecialized_iff

-- Variable template lookup.
#audit Overload.coherence
#audit Overload.coherence_ambiguous
#audit Overload.selectInstance_ne_illFormed
#audit Overload.stability
#audit Overload.stability_other_typeclass

-- Overload resolution and the ranking.
#audit Overload.generate_agree_of_no_perfect
#audit Overload.resolve_agree_of_no_perfect
#audit Overload.generate_p3606_suppresses
#audit Overload.generate_differ_implies_perfect
#audit Overload.betterFunction_iff
#audit Overload.bestViable_iff
#audit Overload.resolve_iff
#audit Overload.resolve_congr
#audit Overload.better_iff
#audit Overload.better_asymm
#audit Overload.separability
#audit Overload.separability_step_order
#audit Overload.separability_argument_identity
#audit Overload.separability_argument_conversion
#audit Overload.separability_tie_break_reach
#audit Overload.separability_rank_precedence
#audit Overload.ranking_live

-- Erasing derivation, Mandates, SFINAE, dispatch, access.
#audit Overload.inheritance_erasure
#audit Overload.derives_erase
#audit Overload.ics_erase
#audit Overload.better_erase
#audit Overload.allBases_erase
#audit Overload.mandate_inertness
#audit Overload.mandate_inertness_index
#audit Overload.invoke_selected
#audit Overload.invoke_of_selected
#audit Overload.constraint_promotion
#audit Overload.deduceTemplate_promote
#audit Overload.promotion_reorders
#audit Overload.deduceTemplate_enableIf
#audit Overload.sfinae_requires
#audit Overload.sfinae_requires_resolve
#audit Overload.sfinae_loses_subsumption
#audit Overload.sfinae_unshielded
#audit Overload.dispatch_styles
#audit Overload.dispatch_hard_condition
#audit Overload.call_eq_invoke
#audit Overload.protected_base_selected_ill_formed
#audit Overload.protected_base_deduced_ill_formed

-- Translation units.
#audit Overload.verdicts_single
#audit Overload.missing_instance_verdict
#audit Overload.late_instance_verdict
#audit Overload.late_insertion_verdict
#audit Overload.callAt_insert_after
#audit Overload.registry_verdicts
#audit Overload.registry_verdicts_single
#audit Overload.registry_late_verdict

/-! ## The typeclass encoding -/

-- The operation object and its routes.
#audit Overload.Typeclass.fmapObject_outcome
#audit Overload.Typeclass.fmapObject_deduce
#audit Overload.Typeclass.call_stability
#audit Overload.Typeclass.pinned_deduce
#audit Overload.Typeclass.unpinned_deduce
#audit Overload.Typeclass.byValue_omitted_outcome
#audit Overload.Typeclass.byValue_passed

-- Inheritance between instance types.
#audit Overload.Typeclass.rank_beats_refinement
#audit Overload.Typeclass.erasure_needs_exact_type
#audit Overload.Typeclass.derived_class_deduction
#audit Overload.Typeclass.superclass_identity

-- Translation units.
#audit Overload.Typeclass.operation_object_not_separated
#audit Overload.Typeclass.byValue_separated
#audit Overload.Typeclass.call_stability_unit

-- Members, arity, algorithms.
#audit Overload.Typeclass.fmapObject_member
#audit Overload.Typeclass.member_transfer
#audit Overload.Typeclass.ofProgram_member
#audit Overload.Typeclass.inaccurate_member_ill_formed
#audit Overload.Typeclass.arity_disjoint_soft
#audit Overload.Typeclass.call_stability_arity
#audit Overload.Typeclass.arity_order_matters
#audit Overload.Typeclass.algorithm_transfer
#audit Overload.Typeclass.algorithm_accurate
#audit Overload.Typeclass.call_order_matters
