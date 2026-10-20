-- OverloadTest/Units.lean                                            -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of linkage, the same entity across units, and the verdict of
the one-definition rule at a lookup. -/

open Overload

private def int : Ty := .named "int"
private def box (t : Ty) : Ty := .spec' "box" [t]

-- Every name of the fragment has external linkage; partial specializations, uses and dependent calls none.
#guard (Decl.object "fmap" "fmap_fn").linkage == .external
#guard (Decl.lookup "trait").linkage == .external
#guard (Decl.function "f" [int] [.class "C"]).linkage == .external
#guard (Decl.instance "trait" [] (box int)).linkage == .none
#guard (Decl.use "trait" (box int)).linkage == .none
-- The lookup variable template and the operation object are one entity in every unit.
#guard sameEntity (.lookup "trait") (.lookup "trait")
#guard sameEntity (.object "fmap" "fmap_fn") (.object "fmap" "fmap_fn")
#guard !sameEntity (.object "fmap" "fmap_fn") (.object "fmap" "fmap_fn" [.namespace "a"])

-- The one-definition rule's verdict at a lookup, and the verdicts already there.
#guard Units.odrVerdicts [unitWithInstance, unitWithExactInstance] == [.odrMismatch 0 1 "trait" (box int)]
#guard Units.odrVerdicts [unitWithInstance, unitWithInstance] == []
#guard Units.odrVerdicts [unitWithInstance] == []
#guard Units.odrVerdicts [unitWithInstance, unitWithoutInstance] == [.odrMismatch 0 1 "trait" (box int)]
#guard Units.verdicts [unitWithInstance, unitWithoutInstance] != []
