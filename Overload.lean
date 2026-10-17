-- Overload.lean                                                      -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Std
import Overload.Syntax
import Overload.Outcome
import Overload.Deduction
import Overload.Constraint
import Overload.Program
import Overload.Steps
import Overload.Ordering
import Overload.Typeclass
import Overload.Resolution
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
