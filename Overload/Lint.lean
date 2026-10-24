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

`#rests_on decl` lists the sentences of the Standard a declaration rests
on: every citation carried by a declaration of this development in its
transitive dependency closure, with the role each was cited in, the
assumptions among them, and the fields of the environment it consults,
which are the oracles. It is how to tell a trait that is a theorem of
the core rules from one that is primitive or rests on an oracle.
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
        if ((Std.citationsOf? env c).getD #[]).isEmpty then
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
    let entries := Std.ParametricAttribute.allEntries Std.stdAttr env
    let n := entries.foldl (fun acc (_, es) => acc + es.size) 0
    logInfo m!"citations: {n} citations on {entries.size} declarations; every spec constructor is cited and every axiom is tagged"
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

/-! ## What a declaration rests on -/

/-- The name of a citation role. -/
def roleName : Std.Role → String
  | .rule => "rule"
  | .theorem => "theorem"
  | .note => "note"
  | .example => "example"

/-- An auxiliary Lean generates for a type, not a dependency the author
wrote: a recursor, a derived instance, a `sizeOf` lemma. -/
def isAuxiliary (n : Name) : Bool :=
  match n with
  | .str _ s =>
    s.startsWith "inst" || s.startsWith "_sizeOf" || s.startsWith "sizeOf_spec" ||
      ["rec", "recOn", "casesOn", "brecOn", "binductionOn", "below", "ibelow", "noConfusion",
       "noConfusionType", "mk.injEq", "mk.sizeOf_spec"].contains s
  | _ => false

/-- The declarations of this development that `root` depends on,
transitively, through the values and types of definitions and theorems;
`root` itself included. A type or a constructor is recorded, for the
citation it carries, and not entered: a definition that mentions a type
does not rest on every constructor of it, only on the ones it uses.
Recursors, derived instances, matchers and constants outside the
development are not entered either: a `match` names every constructor of
the type it splits on, and splitting on a type is not resting on each
constructor's rule. -/
partial def closure (env : Environment) (root : Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut out : Array Name := #[]
  while h : todo.size > 0 do
    let n := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if !isOurs env n || isAuxiliary n then continue
    -- A matcher names every constructor of the type it splits on, so
    -- pattern matching is not resting on them; constructing a value is.
    if (Lean.Meta.Match.Extension.getMatcherInfo? env n).isSome then continue
    out := out.push n
    match env.find? n with
    | some (.inductInfo _) | some (.ctorInfo _) | some (.recInfo _) | some (.quotInfo _) => pure ()
    | some info =>
      for c in info.getUsedConstantsAsSet do
        todo := todo.push c
    | none => pure ()
  return out

/-- The fields of `Env`, the oracles of the `expression-depth` decision. -/
def oracleFields : List Name :=
  [`Overload.Env.instantiate, `Overload.Env.atomic, `Overload.Env.convertible,
   `Overload.Env.bases, `Overload.Env.initializer]

/-- What a declaration rests on. -/
structure RestsOn where
  /-- Each sentence cited in the closure, with its role and the declaration
  carrying the citation, sorted by sentence. -/
  sentences : Array (Std.Entry × Name)
  /-- The assumptions in the closure, with the axiom carrying each. -/
  assumptions : Array (String × Name)
  /-- The oracle fields the closure consults. -/
  oracles : Array Name
  /-- The size of the closure. -/
  size : Nat

/-- Collect what `root` rests on. -/
def restsOn (env : Environment) (root : Name) : RestsOn := Id.run do
  let decls := closure env root
  let mut sentences : Array (Std.Entry × Name) := #[]
  let mut assumptions : Array (String × Name) := #[]
  let mut oracles : Array Name := #[]
  for d in decls do
    for e in (Std.citationsOf? env d).getD #[] do
      sentences := sentences.push (e, d)
    if let some a := Std.assumptionOf? env d then
      assumptions := assumptions.push (a, d)
    if oracleFields.contains d then
      oracles := oracles.push d
  let sorted := sentences.qsort fun (e₁, d₁) (e₂, d₂) =>
    e₁.cite.key < e₂.cite.key || (e₁.cite.key == e₂.cite.key && d₁.toString < d₂.toString)
  return { sentences := sorted, assumptions, oracles, size := decls.size }

/-- The sentences a declaration rests on, as citation keys without
repetition: the question "is this a theorem of those rules" in one list. -/
def restsOnKeys (env : Environment) (root : Name) : Array String :=
  ((restsOn env root).sentences.map fun (e, _) => e.cite.key).toList.eraseDups.toArray

/-- `#rests_on decl`: the sentences of the Standard, the assumptions and
the oracles a declaration rests on. -/
elab "#rests_on " id:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverload id
  let env ← getEnv
  let r := restsOn env declName
  let mut lines : Array String := #[]
  let mut last := ""
  for (e, d) in r.sentences do
    let key := e.cite.key
    let shown := if key == last then "" else s!"{e.cite}"
    last := key
    lines := lines.push s!"  {shown.pushn ' ' (40 - min 40 shown.length)} {roleName e.role}  {d}"
  let assumed := r.assumptions.map fun (a, d) => s!"  {a} ({d})"
  let oracles := r.oracles.map fun d => s!"  {d}"
  logInfo m!"{declName} rests on {r.sentences.size} citations across {r.size} declarations:\n{String.intercalate "\n" lines.toList}\nassumptions:\n{if assumed.isEmpty then "  none" else String.intercalate "\n" assumed.toList}\noracles consulted:\n{if oracles.isEmpty then "  none" else String.intercalate "\n" oracles.toList}"

end Overload.Lint
