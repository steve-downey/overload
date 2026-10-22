-- Overload/Std.lean                                                  -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Lean

/-!
# Traceability to the Standard

Every rule in the model names the sentence of the Standard it transcribes,
and every statement is filed as a rule, a theorem, or an assumption of ours.
The citation is an attribute, not a comment, so tools can check it:

```lean
@[std rule "temp.deduct.general#5.sentence-6"]
def checkConstraints ...

@[std theorem "temp.func.order#2.sentence-4"]
theorem constraints_only_break_ties ...

@[assumed "single-tu"]
def declaredBeforeUse ...
```

Three checks follow from it (see `Overload.Lint`):

* a lint fails the build when a constructor of a specification relation
  (an inductive tagged `@[specification]`), or any axiom, carries neither a citation
  nor an assumption tag;
* the citation index is generated from the environment (`lake exe citations`);
* when the draft moves, `scripts/drift-check.sh` maps each changed sentence
  to the definitions to re-examine.

A citation is a stable name, a paragraph, and optionally a sentence, per the
`citation-granularity` decision: `temp.deduct.general#5.sentence-6`. Stable
names survive renumbering between drafts; clause numbers do not. The draft
commit every citation is read against is recorded once, in `draftPin`.
-/

open Lean

namespace Overload.Std

/-- The text every citation is read against: the `toolchain-pin` and
`draft-pin` decisions in `docs/decisions.md`. -/
structure DraftPin where
  /-- The tag in the cplusplus/draft repository. -/
  tag : String
  /-- The commit the tag names. -/
  commit : String
  /-- The document number of the working draft at that commit. -/
  document : String
  deriving Repr, Inhabited

/-- The pinned draft. `scripts/drift-check.sh` reads this through
`lake exe citations --pin`. -/
def draftPin : DraftPin :=
  { tag := "n5054"
    commit := "45b03900ecb77e8964ba0c8e5ae1063387c2b7de"
    document := "N5054" }

/-- How a tagged declaration stands to the sentence it cites. -/
inductive Role where
  /-- A normative sentence taken as given: a constructor of a specification
  relation, or a clause of a definition. -/
  | rule
  /-- A statement in the Standard that the model proves from the rules. -/
  | theorem
  /-- A note that asserts a consequence: a proof target, not a rule. -/
  | note
  /-- An example: a test with a stated outcome. -/
  | example
  deriving Repr, BEq, Hashable, Inhabited, DecidableEq

instance : ToString Role where
  toString
    | .rule => "rule"
    | .theorem => "theorem"
    | .note => "note"
    | .example => "example"

/-- A sentence of the Standard, by stable name. -/
structure Citation where
  /-- The stable name, such as `temp.deduct.general`. -/
  stable : String
  /-- The paragraph number within the section. -/
  para : Nat
  /-- The sentence within the paragraph, using the draft's own sentence
  anchors, when the citation is that precise. -/
  sentence : Option Nat := none
  deriving Repr, BEq, Hashable, Inhabited, DecidableEq

instance : ToString Citation where
  toString c :=
    let s := s!"[{c.stable}]/{c.para}"
    match c.sentence with
    | some n => s ++ s!" sentence {n}"
    | none => s

/-- The spelling a citation attribute takes, inverse of `parseCitation`. -/
def Citation.key (c : Citation) : String :=
  let s := s!"{c.stable}#{c.para}"
  match c.sentence with
  | some n => s ++ s!".sentence-{n}"
  | none => s

/-- The link to the draft's rendering of the cited sentence. -/
def Citation.url (c : Citation) : String :=
  let s := s!"https://eel.is/c++draft/{c.stable}#{c.para}"
  match c.sentence with
  | some n => s ++ s!".sentence-{n}"
  | none => s

/-- What a `std` attribute records. -/
structure Entry where
  role : Role
  cite : Citation
  deriving Repr, BEq, Hashable, Inhabited

private def isStableChar (c : Char) : Bool :=
  c.isLower || c.isDigit || c == '.' || c == '_'

private def parseNat (what s : String) : Except String Nat :=
  match s.toNat? with
  | some n => if n = 0 then .error s!"{what} numbers start at 1, got {s}" else .ok n
  | none => .error s!"expected a {what} number, got {s.quote}"

/-- Parse `stable.name#para` or `stable.name#para.sentence-n`. -/
def parseCitation (s : String) : Except String Citation := do
  let form := "a citation is spelled stable.name#para or stable.name#para.sentence-n"
  match s.splitOn "#" with
  | [stable, rest] =>
    if stable.isEmpty || !stable.all isStableChar then
      throw s!"{form}; the stable name {stable.quote} is not lowercase.dotted"
    match rest.splitOn ".sentence-" with
    | [p] => return { stable, para := ← parseNat "paragraph" p }
    | [p, q] =>
      return { stable, para := ← parseNat "paragraph" p, sentence := some (← parseNat "sentence" q) }
    | _ => throw s!"{form}; got {s.quote}"
  | _ => throw s!"{form}; got {s.quote}"

/-- The attribute syntax: `@[std rule "temp.deduct.general#5.sentence-6"]`. -/
syntax (name := std)
  "std " (&"rule" <|> "theorem" <|> &"note" <|> "example") str : attr

/-- The assumption tag: `@[assumed "single-tu"]`, naming the decision-log
entry that records what the model needs and the Standard does not say. -/
syntax (name := assumed) "assumed " str : attr

private partial def firstAtom : Syntax → Option String
  | .atom _ v => some v
  | .ident _ raw _ _ => some raw.toString
  | .node _ _ args => args.findSome? firstAtom
  | _ => none

private partial def firstStrLit : Syntax → Option String
  | stx@(.node _ _ args) =>
    match stx.isStrLit? with
    | some s => some s
    | none => args.findSome? firstStrLit
  | _ => none

private def parseRole (s : String) : Except String Role :=
  match s with
  | "rule" => .ok .rule
  | "theorem" => .ok .theorem
  | "note" => .ok .note
  | "example" => .ok .example
  | _ => .error s!"unknown citation role {s.quote}; expected rule, theorem, note or example"

/-- The `std` attribute. Its parameter survives into the `.olean`, which is
what lets the citation index and the drift check read it back. -/
initialize stdAttr : ParametricAttribute Entry ←
  registerParametricAttribute {
    name := `std
    descr := "cites the sentence of the C++ Standard that a definition transcribes " ++
      "(rule), restates (theorem), or tests (note, example)"
    getParam := fun _ stx => do
      let some roleText := firstAtom stx[1] | throwError "std: missing role"
      let some text := firstStrLit stx[2] | throwError "std: missing citation string"
      let role ← match parseRole roleText with
        | .ok r => pure r
        | .error e => throwError e
      let cite ← match parseCitation text with
        | .ok c => pure c
        | .error e => throwError e
      return { role, cite }
  }

/-- The `assumed` attribute. The string names an entry in `docs/decisions.md`. -/
initialize assumedAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `assumed
    descr := "marks a hypothesis the model needs and the Standard does not state; " ++
      "the string names its decision-log entry"
    getParam := fun _ stx => do
      let some text := firstStrLit stx[1] | throwError "assumed: missing decision name"
      if text.isEmpty then throwError "assumed: the decision name is empty"
      return text
  }

/-- The `specification` tag marks a specification relation or outcome type: an
inductive each of whose constructors must carry a `std` citation. -/
initialize specAttr : TagAttribute ←
  registerTagAttribute `specification
    "specification relation: every constructor must carry a std citation"

/-- The citation recorded for a declaration, if any. -/
def citationOf? (env : Environment) (decl : Name) : Option Entry :=
  stdAttr.getParam? env decl

/-- The assumption recorded for a declaration, if any. -/
def assumptionOf? (env : Environment) (decl : Name) : Option String :=
  assumedAttr.getParam? env decl

/-- Every `(declaration, entry)` pair of a parametric attribute, from the
imported modules and the current one. -/
def ParametricAttribute.allEntries {α : Type} [Inhabited α]
    (attr : ParametricAttribute α) (env : Environment) : Array (Name × α) := Id.run do
  let mut out := #[]
  for i in [0:env.header.moduleNames.size] do
    for e in attr.ext.getModuleEntries env i do
      out := out.push e
  for (n, a) in (attr.ext.getState env).2 do
    out := out.push (n, a)
  return out

/-- Every declaration tagged `@[specification]`. -/
def allSpecTypes (env : Environment) : Array Name := Id.run do
  let mut out := #[]
  for i in [0:env.header.moduleNames.size] do
    for n in specAttr.ext.getModuleEntries env i do
      out := out.push n
  for n in specAttr.ext.getState env do
    out := out.push n
  return out

/-- The paragraphs the plan puts in scope. The citation index reports those
with no counterpart in the model yet. -/
def inScope : List (String × Nat) :=
  [ ("temp.deduct.general", 5), ("temp.deduct.general", 8), ("temp.deduct.general", 12)
  , ("temp.deduct.call", 4), ("temp.deduct.call", 5)
  , ("temp.func.order", 8)
  , ("temp.over.link", 6)
  , ("temp.spec.partial.order", 1)
  , ("temp.constr.atomic", 2), ("temp.constr.atomic", 3)
  , ("temp.type", 2)
  , ("temp.arg.nontype", 1), ("temp.arg.nontype", 3)
  , ("over.match.funcs.general", 8)
  , ("over.match.best.general", 2)
  , ("over.best.ics.general", 7)
  -- Phase 9, declarations and lookup (docs/plan.md, phase 9).
  , ("basic.scope.scope", 4), ("basic.scope.scope", 6)
  , ("basic.lookup.general", 1), ("basic.lookup.general", 2), ("basic.lookup.general", 3)
  , ("basic.lookup.unqual", 2), ("basic.lookup.unqual", 3)
  , ("basic.lookup.argdep", 1), ("basic.lookup.argdep", 3), ("basic.lookup.argdep", 4)
  , ("over.call.func", 3), ("over.call.object", 1)
  , ("class.member.lookup", 3), ("class.member.lookup", 4), ("class.member.lookup", 5)
  , ("class.member.lookup", 6)
  , ("temp.dep.general", 2), ("temp.res.general", 1), ("temp.point", 1)
  , ("temp.dep.candidate", 1), ("temp.spec.partial.general", 7)
  , ("basic.link", 8), ("basic.def.odr", 16)
  -- Phase 10, template arguments and their conversion (docs/plan.md, phase 10).
  , ("temp.deduct.general", 2)
  , ("temp.arg.nontype", 2), ("temp.arg.nontype", 4), ("temp.arg.nontype", 5)
  , ("temp.arg.nontype", 6)
  , ("temp.arg.general", 1), ("temp.names", 13), ("temp.type", 1), ("temp.param", 11)
  , ("temp.param", 12)
  , ("expr.const.const", 8), ("dcl.init.list", 7), ("lex.icon", 3)
  , ("basic.fundamental", 1), ("basic.fundamental", 4) ]

end Overload.Std
