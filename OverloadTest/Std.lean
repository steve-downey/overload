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

-- A second `std` attribute on one declaration is refused, and the first
-- stays. The alternative, a parametric attribute's default, is that the
-- second replaces the first in silence.
/--
error: std: twiceCited already carries citations; a second std attribute would replace them. Cite several sentences in one attribute: @[std role "a" "b"]
-/
#guard_msgs in
@[std rule "temp.type#1", std rule "temp.type#2"] def twiceCited : Nat := 0

open Lean Elab Command in
run_cmd do
  let some #[e] := citationsOf? (← getEnv) ``twiceCited
    | throwError "twiceCited should keep its first citation and only that"
  unless e.cite.stable == "temp.type" && e.cite.para == 1 do
    throwError "twiceCited should cite [temp.type]/1, not {e.cite}"

-- The attributes survive into the environment: a cited constructor, a
-- tagged assumption, and an uncited declaration.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some #[e] := citationsOf? env ``Overload.Subst.hard
    | throwError "Subst.hard lost its citation"
  unless e.role == .rule && e.cite.stable == "temp.deduct.general" && e.cite.para == 8 do
    throwError "Subst.hard cites {e.cite}, expected [temp.deduct.general]/8"
  -- Several citations in one attribute are all kept.
  let some es := citationsOf? env ``Overload.Program.userSequence
    | throwError "userSequence lost its citations"
  unless es.size == 4 && es.any (·.cite.stable == "over.best.ics.general") do
    throwError "userSequence should carry four citations"
  unless assumptionOf? env ``Overload.SingleTranslationUnit == some "single-tu" do
    throwError "SingleTranslationUnit lost its assumption tag"
  unless (citationsOf? env ``Overload.bindArg).isNone do
    throwError "bindArg is not cited and should not be"
  unless (Overload.Lint.missingCitations env).isEmpty do
    throwError "the lint reports missing citations"
  unless (Overload.Lint.untaggedAxioms env).isEmpty do
    throwError "the lint reports untagged axioms"
