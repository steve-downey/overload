-- Overload/Lint.lean                                                 -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Std

/-!
# The citation lint and the axiom audit

`#check_citations` fails the build when a constructor of a `@[specification]`
inductive carries no `std` citation, or when an axiom of this development
carries no `assumed` tag. It runs at the end of `Overload.lean`, so every
module is covered.

`#audit decl` checks that a headline theorem rests only on Lean's standard
axioms (`propext`, `Classical.choice`, `Quot.sound`) and tagged
assumptions. A `sorry` is an axiom too, so a theorem that is not finished
fails its audit.

`#check_layering` fails the build when a module of the Standard side,
`Overload.*` outside `Overload.Typeclass`, imports a module of the
typeclass side. The Standard side is meant to stand alone.
-/

open Lean Elab Command

namespace Overload.Lint

/-- The module a declaration was defined in, or `none` for the module being
elaborated. -/
def moduleOf? (env : Environment) (decl : Name) : Option Name :=
  (env.getModuleIdxFor? decl).map fun i => env.header.moduleNames[i.toNat]!

/-- Was `decl` defined in this development, rather than in Lean or a
dependency? The current module always counts as ours. -/
def isOurs (env : Environment) (decl : Name) : Bool :=
  match moduleOf? env decl with
  | some m => Name.isPrefixOf `Overload m
  | none => true

/-- Constructors of `@[specification]` types that carry no citation. -/
def missingCitations (env : Environment) : Array String := Id.run do
  let mut out := #[]
  for t in Std.allSpecTypes env do
    match env.find? t with
    | some (.inductInfo info) =>
      for c in info.ctors do
        if (Std.citationOf? env c).isNone then
          out := out.push s!"constructor {c} of the @[specification] relation {t} carries no std citation"
    | some _ => out := out.push s!"@[specification] {t} is not an inductive type"
    | none => out := out.push s!"@[specification] {t} is not in the environment"
  return out

/-- Axioms of this development that carry no `assumed` tag. -/
def untaggedAxioms (env : Environment) : Array String :=
  env.constants.fold (init := #[]) fun out name info =>
    match info with
    | .axiomInfo _ =>
      if isOurs env name && (Std.assumptionOf? env name).isNone then
        out.push s!"axiom {name} carries no assumed tag"
      else out
    | _ => out

/-- Fail the build unless every spec constructor is cited and every axiom
of ours is tagged. -/
elab "#check_citations" : command => do
  let env ← getEnv
  let problems := missingCitations env ++ untaggedAxioms env
  if problems.isEmpty then
    let n := (Std.ParametricAttribute.allEntries Std.stdAttr env).size
    logInfo m!"citations: {n} tagged declarations; every spec constructor is cited and every axiom is tagged"
  else
    throwError m!"citation lint failed:\n{String.intercalate "\n" problems.toList}"

/-- Is the module on the typeclass side of the model? -/
def isTypeclassModule (m : Name) : Bool := Name.isPrefixOf `Overload.Typeclass m

/-- Modules of the Standard side that import the typeclass side. -/
def layeringBreaches (env : Environment) : Array String := Id.run do
  let mut out := #[]
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if Name.isPrefixOf `Overload m && !isTypeclassModule m then
      for imp in env.header.moduleData[i]!.imports do
        if isTypeclassModule imp.module then
          out := out.push s!"{m} imports {imp.module}"
  return out

/-- Fail the build if the Standard side imports the typeclass side. -/
elab "#check_layering" : command => do
  let env ← getEnv
  let breaches := layeringBreaches env
  if breaches.isEmpty then
    logInfo m!"layering: no module of the Standard side imports Overload.Typeclass"
  else
    throwError m!"layering check failed:\n{String.intercalate "\n" breaches.toList}"

/-- The axioms a headline theorem may rest on without a tag. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `#audit decl`: the theorem rests only on Lean's standard axioms and on
tagged assumptions. -/
elab "#audit " id:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverload id
  let axioms ← liftCoreM <| collectAxioms declName
  let env ← getEnv
  let untagged := axioms.filter fun ax =>
    !(standardAxioms.contains ax || (Std.assumptionOf? env ax).isSome)
  if untagged.isEmpty then
    let assumed := axioms.filterMap fun ax => (Std.assumptionOf? env ax).map fun d => s!"{ax} ({d})"
    let standard := axioms.filter standardAxioms.contains
    logInfo m!"{declName} rests on standard axioms {standard.toList} and assumptions {assumed.toList}"
  else
    throwError m!"{declName} depends on untagged axioms: {untagged.toList}"

end Overload.Lint
