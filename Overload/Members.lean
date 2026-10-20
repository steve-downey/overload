-- Overload/Members.lean                                              -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Adl

/-!
# Member name lookup, and a call on an object

A search in a class scope is not a single search: it is the lookup set
of [class.member.lookup]/2 to /5, a declaration set and the subobjects
the declarations were found in. The class's own declarations, when there
are any, are the whole result (/3), so a member declared in a derived
class hides every base declaration of its name whatever the signatures.
Otherwise the lookup sets of the direct bases are merged (/4), with the
rule of /5: a set found in a base subobject of one already found is
hidden, differing declaration sets from unrelated subobjects make the
set invalid, and the same declarations in several subobjects are shared.
An invalid set is ill-formed (/6).

* Members are declarations whose scope ends in their class
  (`Program.memberScope?`). A subobject is the path of classes from the
  class searched down to it; with no virtual bases, two paths are two
  subobjects.
* `Program.declarationSet` (/3), `LookupSet.merge` (/5),
  `Program.lookupSet` (/4, with the derivation depth bounded by the
  program as `allBases` bounds it), `Program.memberSearch` (/6). The
  relation `LookupSetRel` and `lookupSet_iff` are the agreement.
* A call on an object of class type resolves over the function call
  operators of its class, the result of a search for `operator()` in its
  scope ([over.call.object]/1, [over.match.call.general]/1). Every call
  operator the fragment has is a const member of one class, so the
  implicit object parameter converts alike for all and is left out, as
  the candidates are resolved over the explicit arguments.
* `Program.callCandidates` and `Program.callAt`: what a call from a point
  resolves over, through the lookup of the callee and then, for an
  object, of its call operators.

The theorems: `derived_member_hides_base`, the class's own declarations
are the result whatever the bases declare; the example of
[class.member.lookup]/6 with two unrelated bases (`ambiguous_bases_example`);
`object_call_candidates`, a callee bound to an object resolves over its
class's call operators and nothing else; and `deduceTemplate_at` with
`resolve_at_single`, deduction and resolution see a template through its
head, parameters, return type and constraint, never its name or scope, so
a result about a function template `f` is a result about the same
template as the `operator()` of a class.
-/

namespace Overload

/-! ## The lookup set -/

/-- The scope of a class's members: the class's own scope extended by its
step. -/
def Program.memberScope? (p : Program) (c : String) : Option Scope :=
  (p.classScope? c).map (· ++ [.class c])

/-- The declaration set of a name in a class: a single search in the
class's scope from the point. Complete-class contexts are out of the
fragment, whose uses are all outside every class. -/
@[std rule "class.member.lookup#3.sentence-1"]
def Program.declarationSet (p : Program) (pos : Nat) (c name : String) : List Decl :=
  match p.memberScope? c with
  | some s => singleSearch p pos s name
  | none => []

/-- A subobject, as the path of class names from the class searched down
to it. -/
abbrev Subobject := List String

/-- `q` is a base class subobject of `r`: `r`'s path leads to `q`'s. -/
def Subobject.isBaseOf (q r : Subobject) : Bool := r.isPrefixOf q

/-- A lookup set: the declaration set, `none` once invalid, and the
subobject set. -/
structure LookupSet where
  decls : Option (List Decl)
  subobjects : List Subobject
  deriving Repr, DecidableEq, Inhabited

/-- The empty lookup set. -/
def LookupSet.empty : LookupSet := { decls := some [], subobjects := [] }

/-- Two declaration sets differ, an invalid one differing from any other. -/
def declsDiffer : Option (List Decl) → Option (List Decl) → Bool
  | some a, some b => !(a.all b.contains && b.all a.contains)
  | _, _ => true

/-- Merge the lookup set of a base subobject into the one accumulated: if
every subobject of the base's set is a base subobject of one already
found, or the base's set is empty, nothing changes; conversely the base's
set replaces one whose subobjects are all its bases, or an empty one;
otherwise differing declaration sets make the set invalid, and the same
declarations are shared, with the subobjects united. -/
@[std rule "class.member.lookup#5"]
def LookupSet.merge (acc Bi : LookupSet) : LookupSet :=
  if Bi.subobjects.isEmpty || Bi.subobjects.all (fun q => acc.subobjects.any fun r => q.isBaseOf r) then
    acc
  else if acc.subobjects.isEmpty ||
      acc.subobjects.all (fun r => Bi.subobjects.any fun q => r.isBaseOf q) then
    Bi
  else if declsDiffer acc.decls Bi.decls then
    { decls := none, subobjects := acc.subobjects ++ Bi.subobjects }
  else
    { decls := acc.decls, subobjects := acc.subobjects ++ Bi.subobjects }

/-- The lookup set of a name in a class, reached by the path of classes
`path`, within `fuel` steps of derivation: the class's own declaration
set if it is not empty, and otherwise the lookup sets of its direct
bases merged in turn. -/
@[std rule "class.member.lookup#4"]
def Program.lookupSetWithin (p : Program) (pos : Nat) (name : String) :
    Nat → Subobject → String → LookupSet
  | 0, _, _ => LookupSet.empty
  | fuel + 1, path, c =>
    let here := p.declarationSet pos c name
    if here.isEmpty then
      (p.directBases (.named c)).foldl (fun acc b =>
        match b with
        | .named bn => acc.merge (p.lookupSetWithin pos name fuel (path ++ [c]) bn)
        | _ => acc) LookupSet.empty
    else { decls := some here, subobjects := [path ++ [c]] }

/-- The lookup set of a name in a class. A base is complete before the
class that names it, so a chain of derivation is no longer than the
program, which bounds the search as it bounds `allBases`. -/
def Program.lookupSet (p : Program) (pos : Nat) (c name : String) : LookupSet :=
  p.lookupSetWithin pos name p.length [] c

/-- The result of a search in a class scope: the declaration set of the
lookup set, and an ill-formed program when it is invalid. The
complete-class-context sentence is out of the fragment. -/
@[std rule "class.member.lookup#6"]
def Program.memberSearch (p : Program) (pos : Nat) (c name : String) : Resolution (List Decl) :=
  match (p.lookupSet pos c name).decls with
  | some ds => .selected ds
  | none => .illFormed s!"the lookup of {name} in {c} is ambiguous"

mutual

/-- The lookup set as a relation, within `fuel` steps of derivation. -/
@[specification]
inductive LookupSetRel (p : Program) (pos : Nat) (name : String) :
    Nat → Subobject → String → LookupSet → Prop where
  /-- The derivation bound is exhausted: nothing more is found. The
  bound is the program's length, which no chain of derivation reaches. -/
  | exhausted (path : Subobject) (c : String) : LookupSetRel p pos name 0 path c LookupSet.empty
  /-- The class declares the name: its declaration set, in the class
  itself, and the calculation is complete. -/
  | here (fuel : Nat) (path : Subobject) (c : String) (h : p.declarationSet pos c name ≠ []) :
      LookupSetRel p pos name (fuel + 1) path c
        { decls := some (p.declarationSet pos c name), subobjects := [path ++ [c]] }
  /-- The class does not: the lookup sets of its direct bases, merged in
  turn into the empty set. -/
  | bases (fuel : Nat) (path : Subobject) (c : String) (S : LookupSet)
      (h : p.declarationSet pos c name = [])
      (hm : MergeBases p pos name fuel (path ++ [c]) (p.directBases (.named c)) LookupSet.empty S) :
      LookupSetRel p pos name (fuel + 1) path c S

/-- Merging the lookup sets of a list of direct bases, in turn, into an
accumulated set, within `fuel` steps of derivation below the path. -/
@[specification]
inductive MergeBases (p : Program) (pos : Nat) (name : String) :
    Nat → Subobject → List Ty → LookupSet → LookupSet → Prop where
  /-- No bases left: the accumulated set. -/
  | nil (fuel : Nat) (path : Subobject) (acc : LookupSet) : MergeBases p pos name fuel path [] acc acc
  /-- A direct base: its lookup set is merged, then the rest. -/
  | named (fuel : Nat) (path : Subobject) (bn : String) (bs : List Ty) (acc Sb S : LookupSet)
      (hb : LookupSetRel p pos name fuel path bn Sb)
      (rest : MergeBases p pos name fuel path bs (acc.merge Sb) S) :
      MergeBases p pos name fuel path (.named bn :: bs) acc S
  /-- A base that is not a class by name, which the fragment never
  declares, contributes nothing. -/
  | other (fuel : Nat) (path : Subobject) (b : Ty) (bs : List Ty) (acc S : LookupSet)
      (hb : ∀ bn, b ≠ .named bn) (rest : MergeBases p pos name fuel path bs acc S) :
      MergeBases p pos name fuel path (b :: bs) acc S

end

attribute [std rule "class.member.lookup#4"] LookupSetRel.exhausted
attribute [std rule "class.member.lookup#3"] LookupSetRel.here
attribute [std rule "class.member.lookup#4"] LookupSetRel.bases
attribute [std rule "class.member.lookup#4"] MergeBases.nil
attribute [std rule "class.member.lookup#4"] MergeBases.named
attribute [std rule "class.member.lookup#4"] MergeBases.other

/-- The fold over the bases computes the merge relation. -/
theorem mergeBases_iff (p : Program) (pos : Nat) (name : String) (fuel : Nat) (path : Subobject)
    (ih : ∀ bn S, p.lookupSetWithin pos name fuel path bn = S ↔ LookupSetRel p pos name fuel path bn S) :
    ∀ (bs : List Ty) (acc S : LookupSet),
      bs.foldl (fun acc b =>
        match b with
        | .named bn => acc.merge (p.lookupSetWithin pos name fuel path bn)
        | _ => acc) acc = S ↔ MergeBases p pos name fuel path bs acc S := by
  intro bs
  induction bs with
  | nil =>
    intro acc S
    simp only [List.foldl_nil]
    constructor
    · rintro rfl; exact .nil fuel path acc
    · intro h; cases h; rfl
  | cons b bs ihb =>
    intro acc S
    simp only [List.foldl_cons]
    constructor
    · intro h
      cases b with
      | named bn =>
        exact .named fuel path bn bs acc _ S ((ih bn _).1 rfl) ((ihb _ S).1 h)
      | _ =>
        refine .other fuel path _ bs acc S (fun bn => by simp) ((ihb acc S).1 h)
    · intro h
      cases h with
      | named _ _ bn bs acc Sb S hb rest =>
        rw [← (ih bn Sb).2 hb] at rest
        exact (ihb _ S).2 rest
      | other _ _ b bs acc S hb rest =>
        cases b <;> first | exact absurd rfl (hb _) | exact (ihb acc S).2 rest

/-- The function computes the relation. -/
theorem lookupSetWithin_iff (p : Program) (pos : Nat) (name : String) : ∀ (fuel : Nat)
    (path : Subobject) (c : String) (S : LookupSet),
    p.lookupSetWithin pos name fuel path c = S ↔ LookupSetRel p pos name fuel path c S := by
  intro fuel
  induction fuel with
  | zero =>
    intro path c S
    simp only [Program.lookupSetWithin]
    constructor
    · rintro rfl; exact .exhausted path c
    · intro h; cases h; rfl
  | succ fuel ih =>
    intro path c S
    simp only [Program.lookupSetWithin]
    by_cases h : p.declarationSet pos c name = []
    · simp only [h, List.isEmpty_nil, ↓reduceIte]
      constructor
      · intro hS
        exact .bases fuel path c S h ((mergeBases_iff p pos name fuel (path ++ [c]) (ih _) _ _ S).1 hS)
      · intro hS
        cases hS with
        | bases _ _ _ _ _ hm => exact (mergeBases_iff p pos name fuel (path ++ [c]) (ih _) _ _ S).2 hm
        | here _ _ _ hne => exact absurd h hne
    · simp only [List.isEmpty_eq_false_iff.2 h, Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro rfl; exact .here fuel path c h
      · intro hS
        cases hS with
        | here => rfl
        | bases _ _ _ _ hnil => exact absurd hnil h

theorem lookupSet_iff (p : Program) (pos : Nat) (c name : String) (S : LookupSet) :
    p.lookupSet pos c name = S ↔ LookupSetRel p pos name p.length [] c S :=
  lookupSetWithin_iff p pos name p.length [] c S

/-! ## Hiding and ambiguity -/

/-- A class that declares the name is the whole result: its own
declarations, whatever every base declares and whatever the
signatures. -/
theorem derived_member_hides_base (p : Program) (pos : Nat) (c name : String)
    (h : p.declarationSet pos c name ≠ []) :
    p.memberSearch pos c name = .selected (p.declarationSet pos c name) := by
  have hlen : ∃ n, p.length = n + 1 := by
    cases hp : p.length with
    | zero =>
      exfalso
      apply h
      have : p = [] := List.length_eq_zero_iff.1 hp
      subst this
      simp [Program.declarationSet, Program.memberScope?, Program.classScope?]
    | succ n => exact ⟨n, rfl⟩
  obtain ⟨n, hn⟩ := hlen
  simp only [Program.memberSearch, Program.lookupSet, hn, Program.lookupSetWithin,
    List.isEmpty_eq_false_iff.2 h, Bool.false_eq_true, ↓reduceIte]

/-- The example of [class.member.lookup]/6, as far as the fragment goes:
`struct A { void x(); }; struct B { void x(int); }; struct C : A, B {};`
with the members functions rather than data members. -/
def ambiguousBasesProgram : Program :=
  [ .class "A", .function "x" [] [.class "A"]
  , .class "B", .function "x" [.named "int"] [.class "B"]
  , .class "C" [.named "A", .named "B"] ]

/-- `S(x, C)` is invalid: the two bases declare `x` in unrelated
subobjects, and the declaration sets differ. -/
@[std example "class.member.lookup#6"]
theorem ambiguous_bases_example :
    (ambiguousBasesProgram.lookupSet 5 "C" "x").decls = none ∧
      ambiguousBasesProgram.lookupSet 5 "C" "x" =
        { decls := none, subobjects := [["C", "A"], ["C", "B"]] } ∧
      ∃ e, ambiguousBasesProgram.memberSearch 5 "C" "x" = .illFormed e := by
  refine ⟨by decide, by decide, ⟨_, rfl⟩⟩

/-- `struct D : A { void x(int); }`, over the same `A`: the derived
declaration hides the base's. -/
theorem hiding_member_example :
    Program.memberSearch
        (ambiguousBasesProgram ++ [.class "D" [.named "A"], .function "x" [.named "int"] [.class "D"]])
        7 "D" "x" = .selected [.function "x" [.named "int"] [.class "D"]] := by
  decide

/-! ## A call on an object -/

/-- The function call operators of a class: a search for `operator()` in
its scope. Surrogate call functions are out of the fragment. -/
@[std rule "over.call.object#1.sentence-2"]
def Program.callOperators (p : Program) (pos : Nat) (cls : String) : Resolution (List Decl) :=
  p.memberSearch pos cls "operator()"

/-- The candidates a call resolves over, given what lookup found for its
name: the overload set, or, when the name denotes an object of class
type, the function call operators of its class, one declaration per
entity. Anything else is ill-formed. -/
@[std rule "over.match.call.general#1"]
def Program.candidatesOf (p : Program) (pos : Nat) (found : List Decl) (callee : String) :
    Resolution (List Decl) :=
  match lookupResult found with
  | .overloadSet fs => .selected fs
  | .entity (.object _ cls _) =>
    if (p.classScope? cls).isNone then .illFormed s!"the class {cls} of {callee} is not declared"
    else
      match p.callOperators pos cls with
      | .selected ms => .selected (entities ms)
      | .illFormed e => .illFormed e
      | .noMatch => .illFormed s!"{cls} has no function call operator"
      | .ambiguous _ => .illFormed s!"the function call operators of {cls} are ambiguous"
  | .entity _ => .illFormed s!"{callee} does not denote a function or an object"
  | .none => .illFormed s!"no declaration of {callee} is found"
  | .ambiguous _ => .illFormed s!"the lookup of {callee} is ambiguous"

/-- The candidates a call from a point resolves over: those of what the
call's lookup found. -/
def Program.callCandidates (p : Program) (pos : Nat) (s : Scope) (callee : String)
    (args : List CallArg) : Resolution (List Decl) :=
  p.candidatesOf pos (p.callLookup pos s callee args) callee

/-- A call from a program point in a scope: the candidates, resolved as
`Program.call` does. -/
@[std rule "over.call.func#3.sentence-2"]
def Program.callAt (p : Program) (env : Env) (pos : Nat) (s : Scope) (callee : String)
    (args : List CallArg) (explicit : List Ty := []) : Resolution Candidate :=
  match p.callCandidates pos s callee args with
  | .selected fs => p.call env fs args explicit
  | .illFormed e => .illFormed e
  | .noMatch => .noMatch
  | .ambiguous _ => .illFormed s!"the lookup of {callee} is ambiguous"

/-- A callee that unqualified lookup binds to an object resolves over the
call operators of the object's class and nothing else: argument-dependent
lookup is suppressed, and no function of the name anywhere is a
candidate. -/
theorem object_call_candidates (p : Program) (pos : Nat) (s : Scope) (callee cls : String)
    (sc : Scope) (args : List CallArg)
    (h : unqualifiedLookup p pos s callee = [.object callee cls sc])
    (hcls : (p.classScope? cls).isSome = true) :
    p.callCandidates pos s callee args =
      match p.callOperators pos cls with
      | .selected ms => .selected (entities ms)
      | .illFormed e => .illFormed e
      | .noMatch => .illFormed s!"{cls} has no function call operator"
      | .ambiguous _ => .illFormed s!"the function call operators of {cls} are ambiguous" := by
  have hl : p.callLookup pos s callee args = [.object callee cls sc] := by
    rw [object_suppresses_adl p pos s callee args ⟨_, by rw [h]; exact List.mem_singleton_self _, rfl⟩]
    exact h
  have hnone : (p.classScope? cls).isNone = false := by
    cases h : p.classScope? cls <;> simp_all
  simp [Program.callCandidates, Program.candidatesOf, hl, lookupResult, discardTypes,
    Decl.declaresType, Decl.kind?, Decl.declaresFunction, entities, entities.go, List.filter_cons,
    List.filter_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, hnone]

/-- A member call, `obj.name(args)` on an object of class `cls`: the
members the search finds, resolved over the explicit arguments. -/
def Program.memberCallAt (p : Program) (env : Env) (pos : Nat) (cls name : String)
    (args : List CallArg) (explicit : List Ty := []) : Resolution Candidate :=
  match p.memberSearch pos cls name with
  | .selected ms => p.call env (entities ms) args explicit
  | .illFormed e => .illFormed e
  | .noMatch => .noMatch
  | .ambiguous _ => .illFormed s!"the lookup of {name} in {cls} is ambiguous"

/-! ## A template under another name -/

/-- The same template declared under a name in a scope: the `operator()`
of a class, for one. -/
def FunctionTemplate.at (ft : FunctionTemplate) (name : String) (scope : Scope) : FunctionTemplate :=
  { ft with name := name, scope := scope }

/-- Deduction reads a template's head, parameters, return type and
constraint, never its name or scope: the deduction of a renamed template
is the deduction of the template, with the specialization naming the
renamed one. -/
theorem deduceTemplate_at (env : Env) (ft : FunctionTemplate) (name : String) (scope : Scope)
    (explicit : List Ty) (args : List CallArg) :
    deduceTemplate env (ft.at name scope) explicit args =
      (deduceTemplate env ft explicit args).map (Specialization.withTemplate (ft.at name scope)) := by
  unfold deduceTemplate
  exact bind_map_relabel _ _ _ _ (functionTypeStep_relabel env ft (ft.at name scope) rfl rfl)

/-- Relabel a candidate's specialization to name the renamed template. -/
def Candidate.at (ft : FunctionTemplate) (name : String) (scope : Scope) (c : Candidate) : Candidate :=
  { c with specialization := c.specialization.map (Specialization.withTemplate (ft.at name scope)) }

theorem keeps_at (ft : FunctionTemplate) (name : String) (scope : Scope) :
    Keeps (Candidate.at ft name scope) where
  index _ := rfl
  params _ := rfl
  defaultArgs _ := rfl
  isTemplate c := by simp [Candidate.at, Candidate.isTemplate]

/-- Resolution over one template under another name is resolution over
the template, relabelled: the selected candidate has the same index. -/
theorem resolve_at_single (env : Env) (r : Ranking Conv) (ft : FunctionTemplate) (name : String)
    (scope : Scope) (args : List CallArg) (explicit : List Ty) :
    resolve .text env r [.functionTemplate (ft.at name scope)] args explicit =
      (resolve .text env r [.functionTemplate ft] args explicit).map (Candidate.at ft name scope) := by
  apply resolve_relabel env r [.functionTemplate ft] _ args explicit _ (keeps_at ft name scope)
  · simp only [generate, hasPerfectMatch, List.any_cons, List.any_nil, Bool.or_false, Bool.and_false,
      generate.go, deduceTemplate_at]
    cases deduceTemplate env ft explicit args <;> rfl
  · intro cs hcs c₁ hc₁ c₂ hc₂
    simp only [generate, hasPerfectMatch, List.any_cons, List.any_nil, Bool.or_false, Bool.and_false,
      generate.go] at hcs
    cases hd : deduceTemplate env ft explicit args with
    | ok sp =>
      rw [hd] at hcs
      simp only [Subst.bind_eq, Subst.bind_ok, Bool.false_eq_true, ↓reduceIte] at hcs
      injection hcs with hcs
      subst hcs
      simp only [List.mem_singleton] at hc₁ hc₂
      subst hc₁ hc₂
      simp [orderedC, Candidate.at, Specialization.withTemplate, orderingForCall,
        PartialOrdering.moreSpecialized_irrefl]
    | soft _ =>
      rw [hd] at hcs
      simp at hcs
      subst hcs
      simp at hc₁
    | hard _ =>
      rw [hd] at hcs
      simp at hcs

/-! ## Every earlier case keeps its answer -/

/-- A call from the end of a unit in which every declaration of the name
is a function at global scope resolves over the overload set of the
candidate list. Argument-dependent lookup can add nothing, since every
declaration of the name is already found. -/
theorem callAt_eq_call_global (p : Program) (env : Env) (callee : String) (args : List CallArg)
    (explicit : List Ty)
    (hglobal : ∀ d ∈ p, d.name? = some callee → d.declaresFunction = true ∧ d.scope = [])
    (hsome : p.candidates callee ≠ []) :
    p.callAt env p.length [] callee args explicit = p.call env (p.overloadSet callee) args explicit := by
  have hu : unqualifiedLookup p p.length [] callee = p.candidates callee := by
    simp only [unqualifiedLookup, unqualifiedSearch, List.reverse_nil, unqualifiedSearch.go]
    exact singleSearch_global_eq_candidates p callee hglobal
  have hfn : ∀ d ∈ p.candidates callee, d.declaresFunction = true := by
    intro d hd
    have := List.mem_filter.1 hd
    cases d <;> simp_all [Decl.declaresFunction, Decl.kind?]
  have hadl : ∀ d ∈ p.adl p.length callee args, d ∈ p.candidates callee := by
    intro d hd
    obtain ⟨ns, _, hd', _⟩ := (adl_iff p p.length callee args d).1 hd
    have hmem := List.mem_filter.1 hd'
    rw [List.take_length] at hmem
    have hb := hmem.2
    simp only [Decl.binds, Bool.and_eq_true, beq_iff_eq] at hb
    obtain ⟨-, hs⟩ := hglobal d hmem.1 hb.1
    rw [← hu]
    simp only [unqualifiedLookup, unqualifiedSearch, List.reverse_nil, unqualifiedSearch.go,
      singleSearch, List.take_length, List.mem_filter, Decl.binds, Bool.and_eq_true, beq_iff_eq]
    exact ⟨hmem.1, hb.1, hs⟩
  have hfound : p.callLookup p.length [] callee args = p.candidates callee := by
    simp only [Program.callLookup, hu]
    split
    · rw [List.filter_eq_nil_iff.2 fun d hd => by simp [hadl d hd], List.append_nil]
    · rfl
  obtain ⟨d, ds, hds⟩ : ∃ d ds, p.candidates callee = d :: ds := by
    cases h : p.candidates callee with
    | nil => exact absurd h hsome
    | cons d ds => exact ⟨d, ds, rfl⟩
  have hnotype : ((d :: ds).any fun d => !d.declaresType) = true := by
    refine List.any_eq_true.2 ⟨d, by simp, ?_⟩
    have := hfn d (hds ▸ List.mem_cons_self ..)
    cases d <;> simp_all [Decl.declaresType, Decl.declaresFunction, Decl.kind?]
  have hfilter : (d :: ds).filter (fun d => !d.declaresType) = d :: ds := by
    apply List.filter_eq_self.2
    intro e he
    have := hfn e (hds ▸ he)
    cases e <;> simp_all [Decl.declaresType, Decl.declaresFunction, Decl.kind?]
  have hall : ((d :: ds).all (·.declaresFunction)) = true :=
    List.all_eq_true.2 fun e he => hfn e (hds ▸ he)
  simp only [Program.callAt, Program.callCandidates, Program.candidatesOf, hfound, hds, lookupResult,
    discardTypes, hnotype, ↓reduceIte, hfilter, hall, Program.overloadSet]

/-! ## On programs -/

/-- From `user`, the call `f(1)` with `void f(int);` outside and
`void f(X);` in `user` is not viable, since the inner declaration hides
the outer and an `int` has no associated namespace; a call with an `X`
selects the inner one; and at global scope `f(1)` selects the outer. -/
theorem hiding_call_example :
    (hidingProgram.callAt (Env.ofProgram hidingProgram) 3 [.namespace "user"] "f"
          [{ ty := .named "int" }]).map (·.index) = .noMatch ∧
      (hidingProgram.callAt (Env.ofProgram hidingProgram) 3 [.namespace "user"] "f"
          [{ ty := .named "X" }]).map (·.index) = .selected 0 ∧
      (hidingProgram.callAt (Env.ofProgram hidingProgram) 3 [] "f"
          [{ ty := .named "int" }]).map (·.index) = .selected 0 := by
  refine ⟨by decide, by decide, by decide⟩

/-- `namespace N { struct S { }; void f(S); }`, the example of
[basic.lookup.argdep]/1. The parenthesized call `(f)(s)`, which is not a
call of an unqualified-id, is out of the fragment. -/
def argdepProgram : Program :=
  [ .class "S" [] [] [.namespace "N"], .function "f" [.named "S"] [.namespace "N"] ]

/-- `f(s)` with `s` an `N::S`, written at global scope: unqualified lookup
finds nothing, argument-dependent lookup finds `N::f`, and the call
selects it. -/
@[std example "basic.lookup.argdep#1"]
theorem argdep_1_example :
    unqualifiedLookup argdepProgram 2 [] "f" = [] ∧
      argdepProgram.adl 2 "f" [{ ty := .named "S", lvalue := true }] =
        [.function "f" [.named "S"] [.namespace "N"]] ∧
      (argdepProgram.callAt (Env.ofProgram argdepProgram) 2 [] "f"
          [{ ty := .named "S", lvalue := true }]).map (·.index) = .selected 0 := by
  refine ⟨by decide, by decide, by decide⟩

/-- An operation as a free function template at global scope, and a
user's `fmap(X)` beside the user's class. -/
def freeFunctionProgram : Program :=
  [ .functionTemplate { name := "fmap", head := [{ kind := .type }], params := [.param 0] }
  , .class "X" [] [] [.namespace "user"], .function "fmap" [.named "X"] [.namespace "user"] ]

/-- The same operation as the `operator()` of a class, with an object of
it, and the same user declarations. -/
def objectProgram : Program :=
  [ .class "fmap_fn", .object "fmap" "fmap_fn"
  , .functionTemplate { name := "operator()", head := [{ kind := .type }], params := [.param 0]
                        scope := [.class "fmap_fn"] }
  , .class "X" [] [] [.namespace "user"], .function "fmap" [.named "X"] [.namespace "user"] ]

/-- With the operation a function template, the call `fmap(x)` at global
scope finds the user's function through the argument's namespace, and
it wins as a non-template exact match. With the operation an object,
lookup finds the object and nothing else, the candidates are its
class's call operators, and the call selects the one `operator()`: the
user's function is never a candidate. -/
theorem free_function_admits_adl :
    (freeFunctionProgram.callAt (Env.ofProgram freeFunctionProgram) 3 [] "fmap"
          [{ ty := .named "X" }]).map (·.index) = .selected 1 ∧
      objectProgram.callLookup 5 [] "fmap" [{ ty := .named "X" }] = [.object "fmap" "fmap_fn"] ∧
      objectProgram.callCandidates 5 [] "fmap" [{ ty := .named "X" }] =
        .selected [.functionTemplate { name := "operator()", head := [{ kind := .type }]
                                       params := [.param 0], scope := [.class "fmap_fn"] }] ∧
      (objectProgram.callAt (Env.ofProgram objectProgram) 5 [] "fmap"
          [{ ty := .named "X" }]).map (·.index) = .selected 0 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end Overload
