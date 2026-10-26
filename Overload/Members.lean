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
  (`Program.memberScope?`), a class template's in its scope, which is a
  class scope; the search into a specialization finds the template's
  members and instantiates them with the specialization's arguments
  ([temp.inst]/3, `Program.declarationSet`). A subobject is the path of
  class types from the class searched down to it; with no virtual bases,
  two paths are two subobjects.
* `Program.declarationSet` (/3), `LookupSet.merge` (/5),
  `Program.lookupSet` (/4, with the derivation depth bounded by the
  program as `allBases` bounds it), `Program.memberSearch` (/6). The
  relation `LookupSetRel` and `lookupSet_iff` are the agreement.
* A call on an object of class type resolves over the function call
  operators of its class, the result of a search for `operator()` in its
  scope ([over.call.object]/1, [over.match.call.general]/1), and over
  its surrogate call functions, one for each non-explicit conversion
  function to a pointer or reference to function ([over.call.object]/2).
  The argument list is the implied object argument followed by the
  call's arguments ([over.call.object]/3): a call operator compares it
  against its implicit object parameter, `const X&` for the fragment's
  const members ([over.match.funcs.general]/2, /4), a surrogate against
  its first parameter, the conversion's type, which the object reaches by
  that conversion function. A member call `obj.name(args)` leads with
  the object likewise (`Program.memberCallOn`).
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

/-- The scope of a class type's members: the class's own scope extended
by its step, and for a specialization the class template's, which is a
class scope. -/
@[std rule "basic.scope.class#1"]
def Program.memberScope? (p : Program) (c : Ty) : Option Scope :=
  match ((p.classKey? c).map (·.1) : Option Ty) with
  | some (.named n) => (p.classScope? n).map (· ++ [.class n])
  | some (.spec n _) => (p.classTemplateScope? n).map (· ++ [.class n])
  | _ => none

/-- The declaration set of a name in a class type: a single search in
the class's scope from the point, and for a specialization the
template's declarations found there, instantiated with the
specialization's arguments. Complete-class contexts are out of the
fragment, whose uses are all outside every class. -/
@[std rule "class.member.lookup#3.sentence-1" "temp.inst#3"]
def Program.declarationSet (p : Program) (pos : Nat) (c : Ty) (name : String) : List Decl :=
  match p.memberScope? c, p.classKey? c with
  | some s, some (_, args) => (singleSearch p pos s name).map (Decl.instantiate args)
  | _, _ => []

/-- A class type as a message names it. -/
def Ty.className : Ty → String
  | .named n => n
  | .spec n _ => s!"{n}<...>"
  | t => toString (repr t)

/-- A subobject, as the path of class types from the class searched down
to it. -/
abbrev Subobject := List Ty

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
    Nat → Subobject → Ty → LookupSet
  | 0, _, _ => LookupSet.empty
  | fuel + 1, path, c =>
    let here := p.declarationSet pos c name
    if here.isEmpty then
      (p.directBases c).foldl (fun acc b => acc.merge (p.lookupSetWithin pos name fuel (path ++ [c]) b))
        LookupSet.empty
    else { decls := some here, subobjects := [path ++ [c]] }

/-- The lookup set of a name in a class type. A base is complete before
the class that names it, so a chain of derivation is no longer than the
program, which bounds the search as it bounds `allBases`. -/
def Program.lookupSet (p : Program) (pos : Nat) (c : Ty) (name : String) : LookupSet :=
  p.lookupSetWithin pos name p.length [] c

/-- The result of a search in a class scope: the declaration set of the
lookup set, and an ill-formed program when it is invalid. The
complete-class-context sentence is out of the fragment. -/
@[std rule "class.member.lookup#6"]
def Program.memberSearch (p : Program) (pos : Nat) (c : Ty) (name : String) : Resolution (List Decl) :=
  match (p.lookupSet pos c name).decls with
  | some ds => .selected ds
  | none => .illFormed s!"the lookup of {name} in {c.className} is ambiguous"

mutual

/-- The lookup set as a relation, within `fuel` steps of derivation. -/
@[specification]
inductive LookupSetRel (p : Program) (pos : Nat) (name : String) :
    Nat → Subobject → Ty → LookupSet → Prop where
  /-- The derivation bound is exhausted: nothing more is found. The
  bound is the program's length, which no chain of derivation reaches. -/
  | exhausted (path : Subobject) (c : Ty) : LookupSetRel p pos name 0 path c LookupSet.empty
  /-- The class declares the name: its declaration set, in the class
  itself, and the calculation is complete. -/
  | here (fuel : Nat) (path : Subobject) (c : Ty) (h : p.declarationSet pos c name ≠ []) :
      LookupSetRel p pos name (fuel + 1) path c
        { decls := some (p.declarationSet pos c name), subobjects := [path ++ [c]] }
  /-- The class does not: the lookup sets of its direct bases, merged in
  turn into the empty set. -/
  | bases (fuel : Nat) (path : Subobject) (c : Ty) (S : LookupSet)
      (h : p.declarationSet pos c name = [])
      (hm : MergeBases p pos name fuel (path ++ [c]) (p.directBases c) LookupSet.empty S) :
      LookupSetRel p pos name (fuel + 1) path c S

/-- Merging the lookup sets of a list of direct bases, in turn, into an
accumulated set, within `fuel` steps of derivation below the path. -/
@[specification]
inductive MergeBases (p : Program) (pos : Nat) (name : String) :
    Nat → Subobject → List Ty → LookupSet → LookupSet → Prop where
  /-- No bases left: the accumulated set. -/
  | nil (fuel : Nat) (path : Subobject) (acc : LookupSet) : MergeBases p pos name fuel path [] acc acc
  /-- A direct base: its lookup set is merged, then the rest. -/
  | base (fuel : Nat) (path : Subobject) (b : Ty) (bs : List Ty) (acc Sb S : LookupSet)
      (hb : LookupSetRel p pos name fuel path b Sb)
      (rest : MergeBases p pos name fuel path bs (acc.merge Sb) S) :
      MergeBases p pos name fuel path (b :: bs) acc S

end

attribute [std rule "class.member.lookup#4"] LookupSetRel.exhausted
attribute [std rule "class.member.lookup#3"] LookupSetRel.here
attribute [std rule "class.member.lookup#4"] LookupSetRel.bases
attribute [std rule "class.member.lookup#4"] MergeBases.nil
attribute [std rule "class.member.lookup#4"] MergeBases.base

/-- The fold over the bases computes the merge relation. -/
theorem mergeBases_iff (p : Program) (pos : Nat) (name : String) (fuel : Nat) (path : Subobject)
    (ih : ∀ b S, p.lookupSetWithin pos name fuel path b = S ↔ LookupSetRel p pos name fuel path b S) :
    ∀ (bs : List Ty) (acc S : LookupSet),
      bs.foldl (fun acc b => acc.merge (p.lookupSetWithin pos name fuel path b)) acc = S ↔
        MergeBases p pos name fuel path bs acc S := by
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
      exact .base fuel path b bs acc _ S ((ih b _).1 rfl) ((ihb _ S).1 h)
    · intro h
      cases h with
      | base _ _ b bs acc Sb S hb rest =>
        rw [← (ih b Sb).2 hb] at rest
        exact (ihb _ S).2 rest

/-- The function computes the relation. -/
theorem lookupSetWithin_iff (p : Program) (pos : Nat) (name : String) : ∀ (fuel : Nat)
    (path : Subobject) (c : Ty) (S : LookupSet),
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

theorem lookupSet_iff (p : Program) (pos : Nat) (c : Ty) (name : String) (S : LookupSet) :
    p.lookupSet pos c name = S ↔ LookupSetRel p pos name p.length [] c S :=
  lookupSetWithin_iff p pos name p.length [] c S

/-! ## Hiding and ambiguity -/

/-- A class that declares the name is the whole result: its own
declarations, whatever every base declares and whatever the
signatures. -/
theorem derived_member_hides_base (p : Program) (pos : Nat) (c : Ty) (name : String)
    (h : p.declarationSet pos c name ≠ []) :
    p.memberSearch pos c name = .selected (p.declarationSet pos c name) := by
  have hlen : ∃ n, p.length = n + 1 := by
    cases hp : p.length with
    | zero =>
      exfalso
      apply h
      have : p = [] := List.length_eq_zero_iff.1 hp
      subst this
      cases c <;> simp [Program.declarationSet, Program.memberScope?, Program.classKey?,
        Program.classTemplateDecl?, Program.classScope?]
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
    (ambiguousBasesProgram.lookupSet 5 (.named "C") "x").decls = none ∧
      ambiguousBasesProgram.lookupSet 5 (.named "C") "x" =
        { decls := none, subobjects := [[.named "C", .named "A"], [.named "C", .named "B"]] } ∧
      ∃ e, ambiguousBasesProgram.memberSearch 5 (.named "C") "x" = .illFormed e := by
  refine ⟨by decide, by decide, ⟨_, rfl⟩⟩

/-- `struct D : A { void x(int); }`, over the same `A`: the derived
declaration hides the base's. -/
theorem hiding_member_example :
    Program.memberSearch
        (ambiguousBasesProgram ++ [.class "D" [.named "A"], .function "x" [.named "int"] [.class "D"]])
        7 (.named "D") "x" = .selected [.function "x" [.named "int"] [.class "D"]] := by
  decide

/-! ## A call on an object -/

/-- The function call operators of a class: a search for `operator()` in
its scope. -/
@[std rule "over.call.object#1.sentence-2"]
def Program.callOperators (p : Program) (pos : Nat) (cls : Ty) : Resolution (List Decl) :=
  p.memberSearch pos cls "operator()"

/-- A member function with its implicit object parameter, an lvalue
reference to `const X` for `X` the class type the call is on: every
member function of the fragment is declared `const` and without a
ref-qualifier. A declaration that is not a member is left as it is. -/
@[std rule "over.match.funcs.general#2" "over.match.funcs.general#4"]
def Decl.withImplicitObject (cls : Ty) : Decl → Decl
  | .function n ps sc v ne r =>
    match sc.getLast? with
    | some (.class _) => .function n (.lref (.const cls) :: ps) sc v ne r
    | _ => .function n ps sc v ne r
  | .functionTemplate ft =>
    match ft.scope.getLast? with
    | some (.class _) => .functionTemplate { ft with params := .lref (.const cls) :: ft.params }
    | _ => .functionTemplate ft
  | d => d

/-- The surrogate call functions of a class: for each non-explicit
conversion function it declares to a pointer to function, a reference
to pointer to function or a reference to function of `(P1, ..., Pn)`
returning `R`, the function `R call-function(F, P1, ..., Pn)` with `F`
the conversion's type. The call `(F)(a1, ..., an)` invokes the
conversion function and then the function, so the surrogate is known
not to throw when both are. Conversion functions declared in a base
class are out, as they are for the fragment's conversion sequences. -/
@[std rule "over.call.object#2"]
def Program.surrogates (p : Program) (cls : Ty) : List Decl :=
  (p.conversionsOf cls).filterMap fun
    | .function t false _ ne =>
      let fn : Option (Ty × Ty × Bool) := match t with
        | .ptr (.fn ps r fne) | .lref (.ptr (.fn ps r fne)) | .lref (.fn ps r fne) => some (ps, r, fne)
        | _ => none
      fn.bind fun (ps, r, fne) => ps.toList.map fun params =>
        .function "call-function" (t :: params) [] .none (if ne == some true && fne then some true else none) r
    | _ => none

/-- The candidates of a call on an object of class `cls`: its function
call operators, each with its implicit object parameter, then its
surrogate call functions. A class with neither makes the call
ill-formed. -/
@[std rule "over.call.object#1.sentence-1" "over.call.object#2"]
def Program.objectCandidates (p : Program) (pos : Nat) (cls : Ty) : Resolution (List Decl) :=
  let found : Resolution (List Decl) := match p.callOperators pos cls with
    | .selected ms => .selected ((entities ms).map (Decl.withImplicitObject cls) ++ p.surrogates cls)
    | .noMatch => .selected (p.surrogates cls)
    | .illFormed e => .illFormed e
    | .ambiguous _ => .illFormed s!"the function call operators of {cls.className} are ambiguous"
  match found with
  | .selected [] => .illFormed s!"{cls.className} has no function call operator"
  | r => r

/-- The implied object argument of a call on a named object: the object,
an lvalue of its class, `const` since the fragment's objects are
`constexpr`. -/
@[std rule "over.call.object#3.sentence-1" "over.match.funcs.general#3"]
def impliedObject (cls : Ty) : CallArg := { ty := .const cls, lvalue := true }

/-- The candidates a call resolves over and the argument list submitted
to overload resolution, given what lookup found for its name: the
overload set with the call's arguments, or, when the name denotes an
object of class type, the candidates of a call on the object, its call
operators and surrogates, with the implied object argument first.
Anything else is ill-formed. -/
@[std rule "over.match.call.general#1" "over.call.object#3.sentence-1"]
def Program.candidatesOf (p : Program) (pos : Nat) (found : List Decl) (callee : String)
    (args : List CallArg) : Resolution (List Decl × List CallArg) :=
  match lookupResult found with
  | .overloadSet fs => .selected (fs, args)
  | .entity (.object _ cls _) =>
    if (p.classScope? cls).isNone then .illFormed s!"the class {cls} of {callee} is not declared"
    else (p.objectCandidates pos (.named cls)).map fun cs => (cs, impliedObject (.named cls) :: args)
  | .entity _ => .illFormed s!"{callee} does not denote a function or an object"
  | .none => .illFormed s!"no declaration of {callee} is found"
  | .ambiguous _ => .illFormed s!"the lookup of {callee} is ambiguous"

/-- The candidates a call from a point resolves over, and its argument
list: those of what the call's lookup found. -/
def Program.callCandidates (p : Program) (pos : Nat) (s : Scope) (callee : String)
    (args : List CallArg) : Resolution (List Decl × List CallArg) :=
  p.candidatesOf pos (p.callLookup pos s callee args) callee args

/-- A call from a program point in a scope: the candidates, resolved as
`Program.call` does over the argument list submitted. -/
@[std rule "over.call.func#3.sentence-2"]
def Program.callAt (p : Program) (env : Env) (pos : Nat) (s : Scope) (callee : String)
    (args : List CallArg) (explicit : List Ty := []) : Resolution Candidate :=
  match p.callCandidates pos s callee args with
  | .selected (fs, as) => p.call env fs as explicit
  | .illFormed e => .illFormed e
  | .noMatch => .noMatch
  | .ambiguous _ => .illFormed s!"the lookup of {callee} is ambiguous"

/-- A call on an object of class `cls`, `obj(args)` with `obj` the implied
object argument: the class's call operators and surrogates, resolved
over the object followed by the arguments. -/
@[std rule "over.call.object#3.sentence-1"]
def Program.objectCallAt (p : Program) (env : Env) (pos : Nat) (cls : Ty) (obj : CallArg)
    (args : List CallArg) (explicit : List Ty := []) : Resolution Candidate :=
  match p.objectCandidates pos cls with
  | .selected cs => p.call env cs (obj :: args) explicit
  | .illFormed e => .illFormed e
  | .noMatch => .noMatch
  | .ambiguous _ => .illFormed s!"the function call operators of {cls.className} are ambiguous"

/-- A callee that unqualified lookup binds to an object resolves over the
candidates of a call on the object, its class's call operators and
surrogates, with the object as the first argument, and nothing else:
argument-dependent lookup is suppressed, and no function of the name
anywhere is a candidate. -/
theorem object_call_candidates (p : Program) (pos : Nat) (s : Scope) (callee cls : String)
    (sc : Scope) (args : List CallArg)
    (h : unqualifiedLookup p pos s callee = [.object callee cls sc])
    (hcls : (p.classScope? cls).isSome = true) :
    p.callCandidates pos s callee args =
      (p.objectCandidates pos (.named cls)).map fun cs => (cs, impliedObject (.named cls) :: args) := by
  have hl : p.callLookup pos s callee args = [.object callee cls sc] := by
    rw [object_suppresses_adl p pos s callee args ⟨_, by rw [h]; exact List.mem_singleton_self _, rfl⟩]
    exact h
  have hnone : (p.classScope? cls).isNone = false := by
    cases h : p.classScope? cls <;> simp_all
  simp [Program.callCandidates, Program.candidatesOf, hl, lookupResult, discardTypes,
    Decl.declaresType, Decl.kind?, Decl.declaresFunction, entities, entities.go, List.filter_cons,
    List.filter_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, hnone]

/-- A member call `obj.name(args)` with `obj` the implied object
argument, of class type `cls`: the members the search finds, each with
its implicit object parameter, resolved over the object followed by the
arguments. -/
@[std rule "over.match.funcs.general#2" "over.match.funcs.general#3"]
def Program.memberCallOn (p : Program) (env : Env) (pos : Nat) (cls : Ty) (obj : CallArg)
    (name : String) (args : List CallArg) (explicit : List Ty := []) : Resolution Candidate :=
  match p.memberSearch pos cls name with
  | .selected ms => p.call env ((entities ms).map (Decl.withImplicitObject cls)) (obj :: args) explicit
  | .illFormed e => .illFormed e
  | .noMatch => .noMatch
  | .ambiguous _ => .illFormed s!"the lookup of {name} in {cls.className} is ambiguous"

/-- A member call, `obj.name(args)` on a named object of class type
`cls`, a `const` lvalue as the fragment's objects are. -/
def Program.memberCallAt (p : Program) (env : Env) (pos : Nat) (cls : Ty) (name : String)
    (args : List CallArg) (explicit : List Ty := []) : Resolution Candidate :=
  p.memberCallOn env pos cls (impliedObject cls) name args explicit

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
class's call operators with their implicit object parameter, the
argument list begins with the object, and the call selects the one
`operator()`: the user's function is never a candidate. -/
theorem free_function_admits_adl :
    (freeFunctionProgram.callAt (Env.ofProgram freeFunctionProgram) 3 [] "fmap"
          [{ ty := .named "X" }]).map (·.index) = .selected 1 ∧
      objectProgram.callLookup 5 [] "fmap" [{ ty := .named "X" }] = [.object "fmap" "fmap_fn"] ∧
      objectProgram.callCandidates 5 [] "fmap" [{ ty := .named "X" }] =
        .selected ([.functionTemplate { name := "operator()", head := [{ kind := .type }]
                                        params := [.lref (.const (.named "fmap_fn")), .param 0]
                                        scope := [.class "fmap_fn"] }],
                   [impliedObject (.named "fmap_fn"), { ty := .named "X" }]) ∧
      (objectProgram.callAt (Env.ofProgram objectProgram) 5 [] "fmap"
          [{ ty := .named "X" }]).map (·.index) = .selected 0 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## Surrogate call functions -/

/-- `int f1(int); int f2(B); using fp1 = int(*)(int); using fp2 = int(*)(B);
struct A { operator fp1() const; operator fp2() const; }; A a;`: the
draft's example with a class in place of `float`, which the fragment
lacks. -/
def surrogateProgram : Program :=
  [ .class "B", .class "A"
  , .converting (.named "A") (.function (.ptr (.fn' [.named "int"] (.named "int"))))
  , .converting (.named "A") (.function (.ptr (.fn' [.named "B"] (.named "int"))))
  , .object "a" "A" ]

/-- `a(1)` calls `f1` through the pointer the first conversion function
returns: the surrogate of `fp1` is the only viable candidate. -/
@[std example "over.call.object#3"]
theorem surrogate_example :
    surrogateProgram.objectCandidates 5 (.named "A") =
      .selected [ .function "call-function" [.ptr (.fn' [.named "int"] (.named "int")), .named "int"] [] .none none (.named "int")
                , .function "call-function" [.ptr (.fn' [.named "B"] (.named "int")), .named "B"] [] .none none (.named "int") ] ∧
    (surrogateProgram.callAt (Env.ofProgram surrogateProgram) 5 [] "a" [{ ty := .named "int" }]).map (·.index) =
      .selected 0 := by
  refine ⟨by decide, by decide⟩

/-- A class with a call operator and a conversion to a pointer to
function of the same parameters: `a(1)` selects the call operator. Its
implicit object parameter binds the object by the identity, the
surrogate's first parameter needs the conversion function, and on the
other argument the two are the same. -/
def operatorAndSurrogateProgram : Program :=
  [ .class "A", .function "operator()" [.named "int"] [.class "A"] .none none (.named "int")
  , .converting (.named "A") (.function (.ptr (.fn' [.named "int"] (.named "int"))))
  , .object "a" "A" ]

@[std note "over.call.object#3"]
theorem operator_beats_surrogate :
    (operatorAndSurrogateProgram.callAt (Env.ofProgram operatorAndSurrogateProgram) 4 [] "a"
      [{ ty := .named "int" }]).map (·.index) = .selected 0 := by
  decide

/-- Two conversion functions to the same pointer to function, through a
`const` and a non-const reference, give two surrogates with identical
parameters: no call to either is uniquely better, and the call is
ambiguous, as the paragraph's footnote says. -/
def twoSurrogatesProgram : Program :=
  [ .class "A"
  , .converting (.named "A") (.function (.ptr (.fn' [.named "int"] (.named "int"))))
  , .converting (.named "A") (.function (.lref (.ptr (.fn' [.named "int"] (.named "int")))))
  , .object "a" "A" ]

@[std note "over.call.object#2"]
theorem surrogates_ambiguous :
    ((twoSurrogatesProgram.callAt (Env.ofProgram twoSurrogatesProgram) 4 [] "a"
      [{ ty := .named "int" }]).map (·.index) matches .ambiguous _) = true := by
  decide

end Overload
