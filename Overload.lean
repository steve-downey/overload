-- Overload.lean                                                      -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Std
import Overload.Syntax
import Overload.Outcome
import Overload.Deduction
import Overload.Constraint
import Overload.Program
import Overload.Steps
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
