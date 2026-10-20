-- Overload/Adl.lean                                                  -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Names

/-!
# Argument-dependent lookup, and the candidates of a call

When the callee of a function call is an unqualified name and unqualified
lookup finds nothing that stops it, the lookup also includes
argument-dependent lookup: the function and function template
declarations of the name found by a search in each associated namespace
of the arguments ([basic.lookup.argdep]/1, /3, /4). It is stopped by a
class member, a block-scope function, or any declaration that is not a
function or function template: a variable, for one.

* The associated entities of an argument type
  (`Program.associatedEntities`, `AssociatedEntity`,
  `associatedEntities_iff`): for a class, the class and its bases; for a
  class template specialization, the specialization and the entities of
  its type template arguments; through cv-qualification, pointers and
  references, those of the referenced type; none for a fundamental
  type. Enclosing classes, enumerations, function types and pointers to
  members are out of the fragment. Classes are named by their name
  alone, so two classes of one name in different namespaces are outside
  the fragment too.
* The associated namespaces (`Program.associatedNamespaces`): the
  innermost enclosing namespace of each associated entity.
* The lookup itself (`Program.adl`, `Adl`, `adl_iff`), when it applies
  (`adlApplies`), and the lookup of a call's name
  (`Program.callLookup`): unqualified lookup, and argument-dependent
  lookup when it applies.
* `Program.callAt`: a call from a point in a scope, resolved over what
  that lookup found ([over.call.func]/3).

The theorems: a name that unqualified lookup binds to anything that is
not a function suppresses argument-dependent lookup, so a variable named
like the callee is the whole of what lookup finds, whatever the
associated namespaces declare (`object_suppresses_adl`);
argument-dependent lookup adds functions and function templates only,
from associated namespaces only (`adl_functions`, `adl_scope`); and a
program whose declarations of the name are all functions at global scope
resolves a call from the end of the unit as the candidate list did
(`callAt_eq_call_global`). The example of [basic.lookup.argdep]/1 is a
theorem (`argdep_1_example`), and `free_function_admits_adl` is the
contrast the typeclass encoding rests on: with the operation an object, a
user's function of the same name in the argument's namespace is never a
candidate; with it a function template, that function is found and wins.
-/

namespace Overload

/-! ## Associated entities -/

/-- The scope of the class the program declares under a name, if any. -/
def Program.classScope? (p : Program) (n : String) : Option Scope :=
  p.findSome? fun
    | .class m _ _ s => if m = n then some s else none
    | _ => none

/-- The scope of the class template the program declares under a name, if
any. -/
def Program.classTemplateScope? (p : Program) (c : String) : Option Scope :=
  p.findSome? fun
    | .classTemplate m _ s => if m = c then some s else none
    | _ => none

mutual

/-- The entities associated with an argument type, named by types: for a
class, the class and its direct and indirect bases; for a class template
specialization, the specialization and the entities associated with its
type template arguments; through cv-qualification, pointers and
references, the entities of the referenced type; none for a fundamental
type or anything else. -/
@[std rule "basic.lookup.argdep#3"]
def Program.associatedEntities (p : Program) : Ty → List Ty
  | .named n =>
    match p.classScope? n with
    | some _ => .named n :: p.allBases (.named n)
    | none => []
  | .spec c as =>
    match p.classTemplateScope? c with
    | some _ => .spec c as :: p.argEntities as
    | none => []
  | .const t | .ptr t | .lref t | .rref t => p.associatedEntities t
  | _ => []

/-- The entities associated with the type template arguments of a chain. -/
def Program.argEntities (p : Program) : Ty → List Ty
  | .cons a rest => (if a.isType then p.associatedEntities a else []) ++ p.argEntities rest
  | _ => []

end

/-- A type is one of the template arguments of a chain. -/
inductive ArgOf : Ty → Ty → Prop where
  | head (a rest : Ty) : ArgOf a (.cons a rest)
  | tail (a b rest : Ty) (h : ArgOf a rest) : ArgOf a (.cons b rest)

/-- Association as a relation, one constructor per bullet of
[basic.lookup.argdep]/3 that the fragment has. -/
@[specification]
inductive AssociatedEntity (p : Program) : Ty → Ty → Prop where
  /-- A class is associated with itself. -/
  | self (n : String) (h : (p.classScope? n).isSome = true) :
      AssociatedEntity p (.named n) (.named n)
  /-- A class is associated with each of its direct and indirect bases. -/
  | base (n : String) (b : Ty) (h : (p.classScope? n).isSome = true)
      (hb : b ∈ p.allBases (.named n)) : AssociatedEntity p (.named n) b
  /-- A class template specialization is associated with itself. -/
  | specialization (c : String) (as : Ty) (h : (p.classTemplateScope? c).isSome = true) :
      AssociatedEntity p (.spec c as) (.spec c as)
  /-- A class template specialization is associated with the entities
  associated with each of its type template arguments. -/
  | typeArgument (c : String) (as a e : Ty) (h : (p.classTemplateScope? c).isSome = true)
      (ha : ArgOf a as) (hty : a.isType = true) (hae : AssociatedEntity p a e) :
      AssociatedEntity p (.spec c as) e
  /-- A cv-qualified type has the entities of the type it qualifies. -/
  | cv (t e : Ty) (h : AssociatedEntity p t e) : AssociatedEntity p (.const t) e
  /-- A pointer has the entities of the type it points to. -/
  | pointer (t e : Ty) (h : AssociatedEntity p t e) : AssociatedEntity p (.ptr t) e
  /-- A reference, where a case spells one, has the entities of the type
  it refers to. -/
  | lvalueReference (t e : Ty) (h : AssociatedEntity p t e) : AssociatedEntity p (.lref t) e
  | rvalueReference (t e : Ty) (h : AssociatedEntity p t e) : AssociatedEntity p (.rref t) e

attribute [std rule "basic.lookup.argdep#3"] AssociatedEntity.self
attribute [std rule "basic.lookup.argdep#3"] AssociatedEntity.base
attribute [std rule "basic.lookup.argdep#3"] AssociatedEntity.specialization
attribute [std rule "basic.lookup.argdep#3"] AssociatedEntity.typeArgument
attribute [std rule "basic.lookup.argdep#3"] AssociatedEntity.cv
attribute [std rule "basic.lookup.argdep#3"] AssociatedEntity.pointer
attribute [std rule "basic.lookup.argdep#3"] AssociatedEntity.lvalueReference
attribute [std rule "basic.lookup.argdep#3"] AssociatedEntity.rvalueReference

/-- The function computes the relation, on types and on argument chains
together. -/
theorem associatedEntities_spec (p : Program) (e : Ty) : ∀ t : Ty,
    (e ∈ p.associatedEntities t ↔ AssociatedEntity p t e) ∧
    (e ∈ p.argEntities t ↔ ∃ a, ArgOf a t ∧ a.isType = true ∧ AssociatedEntity p a e) := by
  intro t
  induction t with
  | named n =>
    refine ⟨?_, by simp [Program.argEntities]; rintro a h; cases h⟩
    cases h : p.classScope? n with
    | none =>
      simp only [Program.associatedEntities, h, List.not_mem_nil, false_iff]
      intro hae
      cases hae <;> simp_all
    | some s =>
      simp only [Program.associatedEntities, h, List.mem_cons]
      constructor
      · rintro (rfl | hb)
        · exact .self n (by simp [h])
        · exact .base n e (by simp [h]) hb
      · intro hae
        cases hae with
        | self => exact .inl rfl
        | base _ _ _ hb => exact .inr hb
  | spec c as ih =>
    refine ⟨?_, by simp [Program.argEntities]; rintro a h; cases h⟩
    cases h : p.classTemplateScope? c with
    | none =>
      simp only [Program.associatedEntities, h, List.not_mem_nil, false_iff]
      intro hae
      cases hae <;> simp_all
    | some s =>
      simp only [Program.associatedEntities, h, List.mem_cons]
      constructor
      · rintro (rfl | hb)
        · exact .specialization c as (by simp [h])
        · obtain ⟨a, ha, hty, hae⟩ := ih.2.1 hb
          exact .typeArgument c as a e (by simp [h]) ha hty hae
      · intro hae
        cases hae with
        | specialization => exact .inl rfl
        | typeArgument _ _ a _ _ ha hty hae => exact .inr (ih.2.2 ⟨a, ha, hty, hae⟩)
  | cons a rest iha ihr =>
    refine ⟨(by simp only [Program.associatedEntities, List.not_mem_nil, false_iff]; intro h; cases h), ?_⟩
    simp only [Program.argEntities, List.mem_append]
    constructor
    · rintro (h | h)
      · split at h
        · next hty => exact ⟨a, .head a rest, hty, iha.1.1 h⟩
        · simp at h
      · obtain ⟨b, hb, hty, hae⟩ := ihr.2.1 h
        exact ⟨b, .tail b a rest hb, hty, hae⟩
    · rintro ⟨b, hb, hty, hae⟩
      cases hb with
      | head => exact .inl (by simp [hty]; exact iha.1.2 hae)
      | tail _ _ hb => exact .inr (ihr.2.2 ⟨b, hb, hty, hae⟩)
  | const t ih =>
    refine ⟨?_, by simp [Program.argEntities]; rintro a h; cases h⟩
    simp only [Program.associatedEntities]
    constructor
    · intro h; exact .cv t e (ih.1.1 h)
    · intro h; cases h with | cv _ _ h => exact ih.1.2 h
  | ptr t ih =>
    refine ⟨?_, by simp [Program.argEntities]; rintro a h; cases h⟩
    simp only [Program.associatedEntities]
    constructor
    · intro h; exact .pointer t e (ih.1.1 h)
    · intro h; cases h with | pointer _ _ h => exact ih.1.2 h
  | lref t ih =>
    refine ⟨?_, by simp [Program.argEntities]; rintro a h; cases h⟩
    simp only [Program.associatedEntities]
    constructor
    · intro h; exact .lvalueReference t e (ih.1.1 h)
    · intro h; cases h with | lvalueReference _ _ h => exact ih.1.2 h
  | rref t ih =>
    refine ⟨?_, by simp [Program.argEntities]; rintro a h; cases h⟩
    simp only [Program.associatedEntities]
    constructor
    · intro h; exact .rvalueReference t e (ih.1.1 h)
    · intro h; cases h with | rvalueReference _ _ h => exact ih.1.2 h
  | _ =>
    refine ⟨?_, by simp [Program.argEntities]; rintro a h; cases h⟩
    simp only [Program.associatedEntities, List.not_mem_nil, false_iff]
    intro h
    cases h

theorem associatedEntities_iff (p : Program) (t e : Ty) :
    e ∈ p.associatedEntities t ↔ AssociatedEntity p t e :=
  (associatedEntities_spec p e t).1

/-! ## Associated namespaces -/

/-- The innermost enclosing namespace of a scope: the scope with its
trailing class steps removed. -/
def Scope.enclosingNamespace (s : Scope) : Scope :=
  (s.reverse.dropWhile fun step => step matches .class _).reverse

/-- The scope of the class or class template an associated entity names. -/
def Program.entityScope? (p : Program) : Ty → Option Scope
  | .named n => p.classScope? n
  | .spec c _ => p.classTemplateScope? c
  | _ => none

/-- The associated namespaces of a call: the innermost enclosing
namespaces of the entities associated with its argument types. Inline
namespaces are out of the fragment. -/
@[std rule "basic.lookup.argdep#4.sentence-1"]
def Program.associatedNamespaces (p : Program) (args : List CallArg) : List Scope :=
  ((args.flatMap fun a => p.associatedEntities a.ty).filterMap fun e =>
    (p.entityScope? e).map Scope.enclosingNamespace).eraseDups

/-! ## The lookup -/

/-- A declaration of a class member: its scope ends in a class. -/
def Decl.isMember (d : Decl) : Bool := d.scope.getLast? matches some (.class _)

/-- Argument-dependent lookup applies when unqualified lookup found no
declaration of a class member, no block-scope function declaration,
which the fragment lacks, and no declaration that is not a function or
function template. -/
@[std rule "basic.lookup.argdep#1"]
def adlApplies (found : List Decl) : Bool :=
  found.all fun d => d.declaresFunction && !d.isMember

/-- Argument-dependent lookup for a name: every declaration of a function
or function template of that name found by a search for it in any
associated namespace of the call. Friends and modules are out of the
fragment. -/
@[std rule "basic.lookup.argdep#4.sentence-2"]
def Program.adl (p : Program) (pos : Nat) (name : String) (args : List CallArg) : List Decl :=
  (p.associatedNamespaces args).flatMap fun ns =>
    (singleSearch p pos ns name).filter (·.declaresFunction)

/-- The lookup as a relation: a function or function template declaration
found by a search in an associated namespace. -/
@[specification]
inductive Adl (p : Program) (pos : Nat) (name : String) (args : List CallArg) (d : Decl) : Prop where
  | found (ns : Scope) (hns : ns ∈ p.associatedNamespaces args)
      (hd : d ∈ singleSearch p pos ns name) (hf : d.declaresFunction = true) : Adl p pos name args d

attribute [std rule "basic.lookup.argdep#4.sentence-2"] Adl.found

theorem adl_iff (p : Program) (pos : Nat) (name : String) (args : List CallArg) (d : Decl) :
    d ∈ p.adl pos name args ↔ Adl p pos name args d := by
  simp only [Program.adl, List.mem_flatMap, List.mem_filter]
  constructor
  · rintro ⟨ns, hns, hd, hf⟩
    exact .found ns hns hd hf
  · intro h
    cases h with
    | found ns hns hd hf => exact ⟨ns, hns, hd, hf⟩

/-- The lookup of a call's name: unqualified lookup, and, when nothing it
found stops it, argument-dependent lookup as well. What both find is
found once. -/
@[std rule "basic.lookup.argdep#1"]
def Program.callLookup (p : Program) (pos : Nat) (s : Scope) (name : String)
    (args : List CallArg) : List Decl :=
  let u := unqualifiedLookup p pos s name
  if adlApplies u then u ++ (p.adl pos name args).filter (!u.contains ·) else u

/-- A call of an unqualified name from a program point in a scope: the
candidate functions are the declarations name lookup found, resolved as
`Program.call` does. A name that denotes an object is a call on that
object, which member lookup will supply; until then it is reported, not
resolved. -/
@[std rule "over.call.func#3.sentence-2"]
def Program.callAt (p : Program) (env : Env) (pos : Nat) (s : Scope) (callee : String)
    (args : List CallArg) (explicit : List Ty := []) : Resolution Candidate :=
  match lookupResult (p.callLookup pos s callee args) with
  | .overloadSet fs => p.call env fs args explicit
  | .none => .illFormed s!"no declaration of {callee} is found"
  | .entity _ => .illFormed s!"{callee} denotes an object; member lookup is not in the model yet"
  | .ambiguous _ => .illFormed s!"the lookup of {callee} is ambiguous"

/-! ## What argument-dependent lookup can and cannot add -/

/-- A name bound to anything but a function suppresses argument-dependent
lookup: what lookup finds is what unqualified lookup found, whatever the
associated namespaces declare. An object named like the callee is the
case the typeclass encoding rests on. -/
theorem object_suppresses_adl (p : Program) (pos : Nat) (s : Scope) (name : String)
    (args : List CallArg) (h : ∃ d ∈ unqualifiedLookup p pos s name, d.declaresFunction = false) :
    p.callLookup pos s name args = unqualifiedLookup p pos s name := by
  have hno : adlApplies (unqualifiedLookup p pos s name) = false := by
    obtain ⟨d, hd, hf⟩ := h
    simp only [adlApplies, List.all_eq_false]
    exact ⟨d, hd, by simp [hf]⟩
  simp [Program.callLookup, hno]

/-- Argument-dependent lookup adds functions and function templates only. -/
theorem adl_functions (p : Program) (pos : Nat) (name : String) (args : List CallArg) (d : Decl)
    (h : d ∈ p.adl pos name args) : d.declaresFunction = true := by
  cases (adl_iff p pos name args d).1 h with
  | found _ _ _ hf => exact hf

/-- Argument-dependent lookup adds declarations of associated namespaces
only. -/
theorem adl_scope (p : Program) (pos : Nat) (name : String) (args : List CallArg) (d : Decl)
    (h : d ∈ p.adl pos name args) : d.scope ∈ p.associatedNamespaces args := by
  cases (adl_iff p pos name args d).1 h with
  | found ns hns hd _ =>
    rw [singleSearch_scope p pos ns name d hd]
    exact hns

/-- Every earlier case keeps its answer: a call from the end of a unit in
which every declaration of the name is a function at global scope
resolves over the overload set of the candidate list. Argument-dependent
lookup can add nothing, since every declaration of the name is already
found. -/
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
  -- Argument-dependent lookup finds only declarations already found.
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
  simp only [Program.callAt, hfound, hds, lookupResult, discardTypes, hnotype, ↓reduceIte, hfilter,
    hall, Program.overloadSet]

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

/-- The same operation as an object of a class, with the same user
declarations. -/
def objectProgram : Program :=
  [ .class "fmap_fn", .object "fmap" "fmap_fn"
  , .class "X" [] [] [.namespace "user"], .function "fmap" [.named "X"] [.namespace "user"] ]

/-- With the operation a function template, the call `fmap(x)` at global
scope finds the user's function through the argument's namespace, and
it wins as a non-template exact match. With the operation an object,
lookup finds the object and nothing else: the user's function is never a
candidate. -/
theorem free_function_admits_adl :
    (freeFunctionProgram.callAt (Env.ofProgram freeFunctionProgram) 3 [] "fmap"
          [{ ty := .named "X" }]).map (·.index) = .selected 1 ∧
      objectProgram.callLookup 4 [] "fmap" [{ ty := .named "X" }] = [.object "fmap" "fmap_fn"] := by
  refine ⟨by decide, by decide⟩

end Overload
