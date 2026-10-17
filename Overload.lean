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
import Overload.Typeclass
import Overload.Resolution
import Overload.Ranking
import Overload.Separability
import Overload.Inheritance
import Overload.Mandates
import Overload.Sfinae
import Overload.Dispatch
import Overload.Units
import Overload.Emit
import Overload.Lint

/-!
# Modelling C++ overload resolution in Lean

The root module imports every module of the model and runs the citation
lint over all of them, so `lake build` fails when a rule is uncited or an
axiom untagged. The headline theorems are audited here as they arrive.
-/

#check_citations

#audit Overload.deduceTy_iff
#audit Overload.deduceTy_det
#audit Overload.Val.equivalent_iff
#audit Overload.defaults_hard_absorbing
#audit Overload.constraint_cannot_guard_default
#audit Overload.constraint_soft_shields_function_type
#audit Overload.deduceTemplate_hard_iff
#audit Overload.generate_agree_of_no_perfect
#audit Overload.resolve_agree_of_no_perfect
#audit Overload.generate_p3606_suppresses
#audit Overload.generate_differ_implies_perfect
#audit Overload.PartialOrdering.moreSpecialized_irrefl
#audit Overload.PartialOrdering.moreSpecialized_asymm
#audit Overload.PartialOrdering.tieBreak_needs_equal_heads
#audit Overload.PartialOrdering.patternMatches_iff
#audit Overload.Constraint.moreConstrained_asymm
#audit Overload.PartialOrdering.select_iff
#audit Overload.PartialOrdering.mostSpecialized_unique
#audit Overload.coherence
#audit Overload.coherence_ambiguous
#audit Overload.selectInstance_ne_illFormed
#audit Overload.stability
#audit Overload.stability_other_typeclass
#audit Overload.Constraint.subsumes_iff
#audit Overload.Constraint.subsumes_refl
#audit Overload.Constraint.subsumes_trans
#audit Overload.Constraint.atLeastAsConstrained_trans
#audit Overload.Constraint.subsumes_satisfied
#audit Overload.Constraint.satisfaction_implication_not_subsumes
#audit Overload.Constraint.subsumes_satisfied_hard
#audit Overload.Constraint.subsumes_example
#audit Overload.Constraint.subsumes_not_antisymm
#audit Overload.fmapObject_outcome
#audit Overload.fmapObject_deduce
#audit Overload.call_stability
#audit Overload.resolve_congr
#audit Overload.pinned_deduce
#audit Overload.unpinned_deduce
#audit Overload.byValue_omitted_outcome
#audit Overload.byValue_passed
#audit Overload.better_iff
#audit Overload.better_asymm
#audit Overload.separability
#audit Overload.separability_step_order
#audit Overload.separability_argument_identity
#audit Overload.separability_argument_conversion
#audit Overload.separability_tie_break_reach
#audit Overload.separability_rank_precedence
#audit Overload.ranking_live
#audit Overload.rank_beats_refinement
#audit Overload.inheritance_erasure
#audit Overload.erasure_needs_exact_type
#audit Overload.superclass_identity
#audit Overload.derives_erase
#audit Overload.ics_erase
#audit Overload.better_erase
#audit Overload.deduceTemplate_congr
#audit Overload.derived_class_deduction
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
#audit Overload.deduceTy_subst
#audit Overload.deduceTy_most_general
#audit Overload.PartialOrdering.moreSpecialized_trans
#audit Overload.PartialOrdering.moreSpecialized_trans_of
#audit Overload.PartialOrdering.atLeastAsSpecialized_trans
#audit Overload.PartialOrdering.tieBreakApplies_trans
#audit Overload.Constraint.moreConstrained_trans
#audit Overload.verdicts_single
#audit Overload.missing_instance_verdict
#audit Overload.late_instance_verdict
#audit Overload.operation_object_not_separated
#audit Overload.byValue_separated
#audit Overload.call_stability_unit
#audit Overload.late_insertion_verdict
#audit Overload.callAt_insert_after
