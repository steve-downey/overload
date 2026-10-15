-- OverloadTest/Std.lean                                              -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of the citation attribute and its parser. -/

open Overload.Std

#guard (parseCitation "temp.deduct.general#5.sentence-6").toOption ==
  some { stable := "temp.deduct.general", para := 5, sentence := some 6 }
#guard (parseCitation "temp.type#2").toOption == some { stable := "temp.type", para := 2 }
#guard (parseCitation "temp.type").toOption.isNone
#guard (parseCitation "temp.type#0").toOption.isNone
#guard (parseCitation "Temp.Type#2").toOption.isNone
#guard (parseCitation "temp.type#2.sentence-x").toOption.isNone
#guard ({ stable := "temp.type", para := 2, sentence := some 3 } : Citation).key == "temp.type#2.sentence-3"
#guard toString ({ stable := "temp.type", para := 2 } : Citation) == "[temp.type]/2"

-- The attributes survive into the environment: a cited constructor, a
-- tagged assumption, and an uncited declaration.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some e := citationOf? env ``Overload.Subst.hard
    | throwError "Subst.hard lost its citation"
  unless e.role == .rule && e.cite.stable == "temp.deduct.general" && e.cite.para == 8 do
    throwError "Subst.hard cites {e.cite}, expected [temp.deduct.general]/8"
  unless assumptionOf? env ``Overload.SingleTranslationUnit == some "single-tu" do
    throwError "SingleTranslationUnit lost its assumption tag"
  unless (citationOf? env ``Overload.bindArg).isNone do
    throwError "bindArg is not cited and should not be"
  unless (Overload.Lint.missingCitations env).isEmpty do
    throwError "the lint reports missing citations"
  unless (Overload.Lint.untaggedAxioms env).isEmpty do
    throwError "the lint reports untagged axioms"
