-- Overload/Names.lean                                                -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Scope
import Overload.Access

/-!
# Name lookup: single search, unqualified search, what a call finds

Name lookup associates a use of a name with the declarations that bind
it, and a call is then resolved over what lookup found
([basic.lookup.general]/1, [over.call.func]/3). The fragment has
namespace scopes and class scopes, program points as positions in a
unit, and no using-directives, using-declarations, inline namespaces,
blocks, modules or friends (`decisions.md#lookup-scope`).

* A program point is a position in the unit's declaration list, and a
  declaration precedes it when its locus, immediately after it, is
  before the point (`follows`, `precedes`).
* A *single search* in a scope for a name from a point finds the
  declarations that precede the point and bind the name in that scope
  (`singleSearch`, `SingleSearch`, `singleSearch_iff`).
* An *unqualified search* in a scope is a single search there, and if it
  finds nothing, an unqualified search in the parent scope; unqualified
  name lookup from a point is an unqualified search in its immediate
  scope (`unqualifiedSearch`, `UnqualifiedSearch`,
  `unqualifiedSearch_iff`, `unqualifiedLookup`).
* What lookup found is an overload set when every declaration is a
  function or function template, one entity, or ambiguous
  (`LookupResult`, `lookupResult`), after classes are discarded when
  anything else was found.
* `Program.callAt` is a call from a point in a scope: lookup, then
  resolution over the overload set.

The theorems: an unqualified search stops at the first enclosing scope
that binds the name, so an inner declaration hides every outer one
whatever its signature (`inner_hides_outer`), and everything found
inhabits one enclosing scope (`unqualifiedSearch_scope`). A program with
every declaration of a name a function at global scope resolves a call
from the end of the unit exactly as the candidate list did
(`callAt_eq_call_global`), which is why no earlier case moves.

Argument-dependent lookup and member lookup follow in their own stages.
-/

namespace Overload

/-! ## Program points -/

/-- A program point is a position in the unit's declaration list: `pos`
is the point before the `pos`th declaration, and `p.length` the point
after the last. A declaration's locus is immediately after it
([basic.scope.pdecl]/1), so point `pos` follows declaration `i` when
`i < pos`. -/
@[std rule "basic.lookup.general#2.sentence-2"]
def follows (pos i : Nat) : Bool := decide (i < pos)

/-- A declaration precedes a program point of its own unit when the
point follows it. The bullets for imported units are out of the
fragment. -/
@[std rule "basic.lookup.general#2.sentence-3"]
def precedes (i pos : Nat) : Bool := follows pos i

/-! ## Binding -/

/-- A declaration binds the names it introduces in its target scope,
which in the fragment is the scope it inhabits. -/
@[std rule "basic.scope.scope#2"]
def Decl.binds (d : Decl) (s : Scope) (name : String) : Bool :=
  d.name? == some name && d.scope == s

/-- The parent scope of a scope: the smallest scope that contains it.
The global scope has none. -/
@[std rule "basic.scope.scope#2"]
def Scope.parent? (s : Scope) : Option Scope :=
  if s.isEmpty then none else some s.dropLast

/-! ## Single search -/

/-- A single search in a scope for a name from a program point finds
every declaration that precedes the point to which the name is bound in
that scope. The declarations that precede point `pos` are the first
`pos` of the unit. -/
@[std rule "basic.lookup.general#3.sentence-1"]
def singleSearch (p : Program) (pos : Nat) (s : Scope) (name : String) : List Decl :=
  (p.take pos).filter (·.binds s name)

/-- The single search as a relation: a declaration is found when it is
in the unit, precedes the point, and binds the name in the scope. -/
@[specification]
inductive SingleSearch (p : Program) (pos : Nat) (s : Scope) (name : String) : Decl → Prop where
  | found (i : Nat) (d : Decl) (hi : p[i]? = some d) (hp : precedes i pos = true)
      (hb : d.binds s name = true) : SingleSearch p pos s name d

attribute [std rule "basic.lookup.general#3.sentence-1"] SingleSearch.found

theorem singleSearch_iff (p : Program) (pos : Nat) (s : Scope) (name : String) (d : Decl) :
    d ∈ singleSearch p pos s name ↔ SingleSearch p pos s name d := by
  simp only [singleSearch, List.mem_filter]
  constructor
  · rintro ⟨hm, hb⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hm
    rw [List.getElem?_take] at hi
    split at hi
    · next h => exact .found i d hi (by simp [precedes, follows, h]) hb
    · simp at hi
  · rintro ⟨i, d, hi, hp, hb⟩
    refine ⟨List.mem_iff_getElem?.2 ⟨i, ?_⟩, hb⟩
    simp only [precedes, follows, decide_eq_true_eq] at hp
    rw [List.getElem?_take]
    simp [hp, hi]

/-- A declaration found in a scope inhabits it. -/
theorem singleSearch_scope (p : Program) (pos : Nat) (s : Scope) (name : String) (d : Decl)
    (h : d ∈ singleSearch p pos s name) : d.scope = s := by
  obtain ⟨_, hb⟩ := List.mem_filter.1 h
  simp only [Decl.binds, Bool.and_eq_true, beq_iff_eq] at hb
  exact hb.2

/-! ## Unqualified search -/

/-- The unqualified search, over the scope path innermost first: a single
search in the scope, and if it finds nothing, the search in the parent. -/
def unqualifiedSearch.go (p : Program) (pos : Nat) (name : String) : List ScopeStep → List Decl
  | [] => singleSearch p pos [] name
  | x :: rest =>
    let here := singleSearch p pos (x :: rest).reverse name
    if here.isEmpty then unqualifiedSearch.go p pos name rest else here

/-- An unqualified search in a scope from a program point: the single
search in that scope, and if no declarations are found, the unqualified
search in the parent scope, if any. Using-directives are out of the
fragment, so a search in a namespace is a single search. -/
@[std rule "basic.lookup.unqual#2"]
def unqualifiedSearch (p : Program) (pos : Nat) (s : Scope) (name : String) : List Decl :=
  unqualifiedSearch.go p pos name s.reverse

/-- The unqualified search as a relation, one constructor per sentence of
[basic.lookup.unqual]/2: found here, or nothing here and the parent's
result, or nothing anywhere. -/
@[specification]
inductive UnqualifiedSearch (p : Program) (pos : Nat) (name : String) : Scope → List Decl → Prop where
  /-- The search in the scope itself found declarations. -/
  | here (s : Scope) (h : singleSearch p pos s name ≠ []) :
      UnqualifiedSearch p pos name s (singleSearch p pos s name)
  /-- Nothing found here: the result of the unqualified search in the
  parent scope. -/
  | parent (s t : Scope) (h : singleSearch p pos s name = []) (hp : Scope.parent? s = some t)
      (r : List Decl) (hr : UnqualifiedSearch p pos name t r) : UnqualifiedSearch p pos name s r
  /-- Nothing found in the global scope, which has no parent. -/
  | global (h : singleSearch p pos [] name = []) : UnqualifiedSearch p pos name [] []

attribute [std rule "basic.lookup.unqual#2.sentence-1"] UnqualifiedSearch.here
attribute [std rule "basic.lookup.unqual#2.sentence-2"] UnqualifiedSearch.parent
attribute [std rule "basic.lookup.unqual#2.sentence-2"] UnqualifiedSearch.global

theorem parent?_concat (l : List ScopeStep) (x : ScopeStep) :
    Scope.parent? (l ++ [x]) = some l := by
  simp [Scope.parent?]

theorem unqualifiedSearch_go_iff (p : Program) (pos : Nat) (name : String) (l : List ScopeStep)
    (r : List Decl) :
    unqualifiedSearch.go p pos name l = r ↔ UnqualifiedSearch p pos name l.reverse r := by
  induction l generalizing r with
  | nil =>
    simp only [unqualifiedSearch.go, List.reverse_nil]
    constructor
    · rintro rfl
      by_cases h : singleSearch p pos [] name = []
      · rw [h]; exact .global h
      · exact .here [] h
    · intro h
      cases h with
      | here _ _ => rfl
      | parent _ t h hp => simp [Scope.parent?] at hp
      | global h => exact h
  | cons x rest ih =>
    simp only [unqualifiedSearch.go, List.reverse_cons]
    constructor
    · rintro rfl
      by_cases h : singleSearch p pos (rest.reverse ++ [x]) name = []
      · simp only [h, List.isEmpty_nil, ↓reduceIte]
        exact .parent _ _ h (parent?_concat _ _) _ ((ih _).1 rfl)
      · simp only [List.isEmpty_eq_false_iff.2 h, Bool.false_eq_true, ↓reduceIte]
        exact .here _ h
    · intro h
      generalize hs : rest.reverse ++ [x] = s at h
      cases h with
      | here s hne =>
        subst hs
        simp [List.isEmpty_eq_false_iff.2 hne]
      | parent s t hnil hp r hr =>
        subst hs
        rw [parent?_concat, Option.some.injEq] at hp
        subst hp
        simp only [hnil, List.isEmpty_nil, ↓reduceIte]
        exact (ih r).2 hr
      | global => simp at hs

/-- The function computes the relation. -/
theorem unqualifiedSearch_iff (p : Program) (pos : Nat) (s : Scope) (name : String)
    (r : List Decl) :
    unqualifiedSearch p pos s name = r ↔ UnqualifiedSearch p pos name s r := by
  have := unqualifiedSearch_go_iff p pos name s.reverse r
  rwa [List.reverse_reverse] at this

/-- Unqualified name lookup from a program point is an unqualified search
in the immediate scope at that point, which a call names. -/
@[std rule "basic.lookup.unqual#3"]
def unqualifiedLookup (p : Program) (pos : Nat) (s : Scope) (name : String) : List Decl :=
  unqualifiedSearch p pos s name

/-- An inner scope hides an outer one: when the immediate scope binds the
name, the unqualified search is the single search there, whatever every
enclosing scope declares and whatever the signatures. -/
theorem inner_hides_outer (p : Program) (pos : Nat) (s : Scope) (name : String)
    (h : singleSearch p pos s name ≠ []) :
    unqualifiedSearch p pos s name = singleSearch p pos s name :=
  (unqualifiedSearch_iff p pos s name _).2 (.here s h)

/-- Everything an unqualified search finds inhabits one scope, an
enclosing one. -/
theorem unqualifiedSearch_scope (p : Program) (pos : Nat) (s : Scope) (name : String) :
    ∃ t, t <+: s ∧ ∀ d ∈ unqualifiedSearch p pos s name, d.scope = t := by
  have h := (unqualifiedSearch_iff p pos s name _).1 rfl
  generalize unqualifiedSearch p pos s name = r at h ⊢
  induction h with
  | here s _ => exact ⟨s, List.prefix_refl _, fun d hd => singleSearch_scope p pos s name d hd⟩
  | parent s t _ hp r _ ih =>
    obtain ⟨u, hu, hall⟩ := ih
    refine ⟨u, hu.trans ?_, hall⟩
    simp only [Scope.parent?] at hp
    split at hp
    · simp at hp
    · rw [Option.some.injEq] at hp
      subst hp
      exact List.dropLast_prefix _
  | global _ => exact ⟨[], List.nil_prefix, by simp⟩

/-! ## What lookup found -/

/-- Declarations of classes are discarded if any other declarations are
found: a type is hidden by any other entity of its name. The fragment has
no enumerations. -/
@[std rule "basic.lookup.general#4.sentence-2"]
def discardTypes (found : List Decl) : List Decl :=
  if found.any (fun d => !d.declaresType) then found.filter (fun d => !d.declaresType) else found

/-- The outcome of name lookup, one constructor per sentence of
[basic.lookup.general]/1. -/
@[specification]
inductive LookupResult where
  /-- No declarations were found: the program is ill-formed. -/
  | none
  /-- Every declaration found denotes a function or function template:
  they form an overload set, one declaration per entity. -/
  | overloadSet (fs : List Decl)
  /-- The declarations found all denote one entity that is not a
  function. -/
  | entity (d : Decl)
  /-- The declarations found do not all denote the same entity: the
  lookup is ambiguous and the program is ill-formed. -/
  | ambiguous (ds : List Decl)
  deriving Repr, DecidableEq, Inhabited

attribute [std rule "basic.lookup.general#1.sentence-3"] LookupResult.none
attribute [std rule "basic.lookup.general#1.sentence-4"] LookupResult.overloadSet
attribute [std rule "basic.lookup.general#1.sentence-5"] LookupResult.entity
attribute [std rule "basic.lookup.general#1.sentence-5"] LookupResult.ambiguous

/-- Classify what lookup found. -/
@[std rule "basic.lookup.general#1"]
def lookupResult (found : List Decl) : LookupResult :=
  match discardTypes found with
  | [] => .none
  | ds =>
    if ds.all (·.declaresFunction) then .overloadSet (entities ds)
    else
      match entities ds with
      | [d] => .entity d
      | es => .ambiguous es

/-! ## A call from a point -/

/-- A call of an unqualified name from a program point in a scope: the
candidate functions are the declarations name lookup found, resolved as
`Program.call` does. A name that denotes an object is a call on that
object, which member lookup will supply; until then it is reported, not
resolved. -/
@[std rule "over.call.func#3.sentence-2"]
def Program.callAt (p : Program) (env : Env) (pos : Nat) (s : Scope) (callee : String)
    (args : List CallArg) (explicit : List Ty := []) : Resolution Candidate :=
  match lookupResult (unqualifiedLookup p pos s callee) with
  | .overloadSet fs => p.call env fs args explicit
  | .none => .illFormed s!"no declaration of {callee} is found"
  | .entity _ => .illFormed s!"{callee} denotes an object; member lookup is not in the model yet"
  | .ambiguous _ => .illFormed s!"the lookup of {callee} is ambiguous"

/-- Over the whole unit, with every declaration of the name a function or
function template at global scope, a single search in the global scope
is the candidate list. -/
theorem singleSearch_global_eq_candidates (p : Program) (callee : String)
    (hglobal : ∀ d ∈ p, d.name? = some callee → d.declaresFunction = true ∧ d.scope = []) :
    singleSearch p p.length [] callee = p.candidates callee := by
  simp only [singleSearch, List.take_length, Program.candidates]
  apply List.filter_congr
  intro d hd
  have hg := hglobal d hd
  clear hglobal
  cases d with
  | function n ps sc =>
    by_cases hn : n = callee
    · subst hn
      obtain ⟨-, hs⟩ := hg (by simp [Decl.name?])
      have hs' : sc = [] := by simpa [Decl.scope] using hs
      simp [Decl.binds, Decl.name?, Decl.scope, hs']
    · simp [Decl.binds, Decl.name?, hn]
  | functionTemplate ft =>
    by_cases hn : ft.name = callee
    · obtain ⟨-, hs⟩ := hg (by simp [Decl.name?, hn])
      have hs' : ft.scope = [] := by simpa [Decl.scope] using hs
      simp [Decl.binds, Decl.name?, Decl.scope, hn, hs']
    · simp [Decl.binds, Decl.name?, hn]
  | «class» m bs ps sc =>
    have : m ≠ callee := fun h => by simp [Decl.name?, Decl.declaresFunction, Decl.kind?, h] at hg
    simp [Decl.binds, Decl.name?, this]
  | classTemplate m h sc =>
    have : m ≠ callee := fun h => by simp [Decl.name?, Decl.declaresFunction, Decl.kind?, h] at hg
    simp [Decl.binds, Decl.name?, this]
  | lookup m =>
    have : m ≠ callee := fun h => by simp [Decl.name?, Decl.declaresFunction, Decl.kind?, h] at hg
    simp [Decl.binds, Decl.name?, this]
  | lookupHard m =>
    have : m ≠ callee := fun h => by simp [Decl.name?, Decl.declaresFunction, Decl.kind?, h] at hg
    simp [Decl.binds, Decl.name?, this]
  | object m cls sc =>
    have : m ≠ callee := fun h => by simp [Decl.name?, Decl.declaresFunction, Decl.kind?, h] at hg
    simp [Decl.binds, Decl.name?, this]
  | concept m body =>
    have : m ≠ callee := fun h => by simp [Decl.name?, Decl.declaresFunction, Decl.kind?, h] at hg
    simp [Decl.binds, Decl.name?, this]
  | «instance» => simp [Decl.binds, Decl.name?]
  | use => simp [Decl.binds, Decl.name?]

/-- Every earlier case keeps its answer: a call from the end of a unit in
which every declaration of the name is a function at global scope
resolves over the overload set of the candidate list. -/
theorem callAt_eq_call_global (p : Program) (env : Env) (callee : String) (args : List CallArg)
    (explicit : List Ty)
    (hglobal : ∀ d ∈ p, d.name? = some callee → d.declaresFunction = true ∧ d.scope = [])
    (hsome : p.candidates callee ≠ []) :
    p.callAt env p.length [] callee args explicit = p.call env (p.overloadSet callee) args explicit := by
  have hfound : unqualifiedLookup p p.length [] callee = p.candidates callee := by
    simp only [unqualifiedLookup, unqualifiedSearch, List.reverse_nil, unqualifiedSearch.go]
    exact singleSearch_global_eq_candidates p callee hglobal
  have hfn : ∀ d ∈ p.candidates callee, d.declaresFunction = true := by
    intro d hd
    have := List.mem_filter.1 hd
    cases d <;> simp_all [Decl.declaresFunction, Decl.kind?]
  have hnotype : (p.candidates callee).any (fun d => !d.declaresType) = true := by
    obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ hsome
    refine List.any_eq_true.2 ⟨d, hd, ?_⟩
    have := hfn d hd
    cases d <;> simp_all [Decl.declaresType, Decl.declaresFunction, Decl.kind?]
  have hfilter : (p.candidates callee).filter (fun d => !d.declaresType) = p.candidates callee := by
    apply List.filter_eq_self.2
    intro d hd
    have := hfn d hd
    cases d <;> simp_all [Decl.declaresType, Decl.declaresFunction, Decl.kind?]
  obtain ⟨d, ds, hds⟩ : ∃ d ds, p.candidates callee = d :: ds := by
    cases h : p.candidates callee with
    | nil => exact absurd h hsome
    | cons d ds => exact ⟨d, ds, rfl⟩
  have hall : ((d :: ds).all (·.declaresFunction)) = true :=
    List.all_eq_true.2 fun e he => hfn e (hds ▸ he)
  rw [hds] at hnotype hfilter
  simp only [Program.callAt, hfound, hds, lookupResult, discardTypes, hnotype, ↓reduceIte, hfilter,
    hall, Program.overloadSet]

/-! ## Hiding, on a program -/

/-- `struct X {}; void f(int);` at global scope and `void f(X);` in
`user`. -/
def hidingProgram : Program :=
  [ .class "X", .function "f" [.named "int"], .function "f" [.named "X"] [.namespace "user"] ]

/-- From `user`, lookup of `f` finds the inner declaration only, so a
call with an `int` is not viable there though the exact match exists
outside, and a call with an `X` selects the inner one; from the global
scope lookup finds the outer declaration. -/
theorem hiding_example :
    unqualifiedLookup hidingProgram 3 [.namespace "user"] "f" =
        [.function "f" [.named "X"] [.namespace "user"]] ∧
      unqualifiedLookup hidingProgram 3 [] "f" = [.function "f" [.named "int"]] ∧
      (hidingProgram.callAt (Env.ofProgram hidingProgram) 3 [.namespace "user"] "f"
          [{ ty := .named "int" }]).map (·.index) = .noMatch ∧
      (hidingProgram.callAt (Env.ofProgram hidingProgram) 3 [.namespace "user"] "f"
          [{ ty := .named "X" }]).map (·.index) = .selected 0 ∧
      (hidingProgram.callAt (Env.ofProgram hidingProgram) 3 [] "f"
          [{ ty := .named "int" }]).map (·.index) = .selected 0 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

end Overload
