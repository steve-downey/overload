-- Overload/Special.lean                                              -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Ranking
import Overload.Types

/-!
# Special member functions

Which special member functions a class has, by [special]/1 and the
implicit declarations of [class.default.ctor], [class.copy.ctor],
[class.copy.assign] and [class.dtor]; which defaulted ones are defined as
deleted; which are trivial; and which are eligible. Every rule about a
subobject is a rule about overload resolution over the subobject's
class, so the judgements are fuel-bounded through the program, as
`derives` is: a member's class is complete before the class that holds
it, so a chain of subobjects is no longer than the program.

The candidate lists and the resolution over them are parametrized by the
facts they consult, `Facts`, so that nothing here is mutually recursive:
`deletedWithin` at one fuel consults the facts at the fuel below.

The value and reference nature of a type, the author's data and codata,
are definitions and theorems here, never rules
(`decisions.md#value-nature`).
-/

namespace Overload

/-- How a class comes to have a special member function: user-provided,
with a body; defaulted, implicitly declared or `= default`; or deleted
on its first declaration, `= delete`, or by the suppression of
[class.copy.ctor]/6 and [class.copy.assign]/2. A defaulted one may
further be defined as deleted, which `Program.deleted` decides. -/
inductive Provenance where
  | userProvided | defaulted | deleted
  deriving Repr, DecidableEq, Inhabited

attribute [std rule "dcl.fct.def.default#5"] Provenance.userProvided Provenance.defaulted
attribute [std rule "dcl.fct.def.delete#1"] Provenance.deleted

/-- A special member function a class has: its kind, its provenance, and
whether its parameter is a reference to `const`. -/
structure Smf where
  kind : SmfKind
  prov : Provenance
  constParam : Bool := true
  deriving Repr, DecidableEq, Inhabited

/-- The parameter types of a special member of class `c`: none for a
default constructor or destructor, `X&` or `const X&` for a copy
constructor or copy assignment operator, `X&&` or `const X&&` for a move
constructor or move assignment operator. -/
@[std rule "class.copy.ctor#1" "class.copy.ctor#2" "class.copy.assign#1" "class.copy.assign#3"]
def Smf.params (c : Ty) (s : Smf) : List Ty :=
  match s.kind with
  | .defaultCtor | .dtor => []
  | .copyCtor | .copyAssign => [.lref (if s.constParam then .const c else c)]
  | .moveCtor | .moveAssign => [.rref (if s.constParam then .const c else c)]

/-- The provenance a user-declared body gives. -/
def SmfBody.prov : SmfBody → Provenance
  | .userProvided => .userProvided
  | .defaulted => .defaulted
  | .deleted => .deleted

namespace Program

/-- A converting constructor whose parameter makes it a copy or move
constructor of its class: `X&` or `const X&`, `X&&` or `const X&&`. It is
user-declared and user-provided. -/
@[std rule "class.copy.ctor#1" "class.copy.ctor#2"]
def copyMoveForm (c : Ty) : UserConv → Option SmfDecl
  | .constructor (.lref t) _ =>
    if t == c then some { kind := .copyCtor, constParam := false }
    else if t == .const c then some { kind := .copyCtor } else none
  | .constructor (.rref t) _ =>
    if t == c then some { kind := .moveCtor, constParam := false }
    else if t == .const c then some { kind := .moveCtor } else none
  | _ => none

/-- The user-declared special member of a kind, if any: a `special`
declaration, or a converting constructor of copy or move form. Two
special members are of the same kind when their kinds agree; the
fragment's have no cv-qualifiers or ref-qualifiers to tell apart. -/
@[std rule "special#5"]
def userDeclared (p : Program) (c : Ty) (k : SmfKind) : Option SmfDecl :=
  (p.specialDecls c ++ (p.conversionsOf c).filterMap (copyMoveForm c)).find? (·.kind == k)

/-- Has the class a user-declared constructor of any form? A converting
constructor is one. -/
@[std rule "class.default.ctor#1"]
def userDeclaredCtor (p : Program) (c : Ty) : Bool :=
  (p.specialDecls c).any (·.kind.isCtor) || (p.conversionsOf c).any (· matches .constructor ..)

/-- The potentially constructed subobjects of a class: its direct
non-static data members, by type, then its direct bases. No class of the
fragment is abstract or has a virtual base. -/
@[std rule "special#7"]
def subobjectsOf (p : Program) (c : Ty) : List Ty :=
  (p.membersOf c).map (·.ty) ++ p.directBases c

/-- The classes of the potentially constructed subobjects of class type,
without their `const`. -/
def classSubobjects (p : Program) (c : Ty) : List Ty :=
  (p.subobjectsOf c).filterMap fun t => if t.stripConst.isClass then some t.stripConst else none

/-! ## Which special members a class has -/

/-- The special member function of kind `k` that class `c` has, within
`fuel` steps of subobject nesting: the user-declared one, or the
implicitly declared one where the rules declare it. The copy
constructor's and copy assignment's parameter form looks at the
subobjects' ([class.copy.ctor]/7, [class.copy.assign]/2). -/
@[std rule "class.default.ctor#1" "class.copy.ctor#6" "class.copy.ctor#7" "class.copy.ctor#8"
  "class.copy.assign#2" "class.copy.assign#4" "class.dtor#2"]
def specialWithin (p : Program) : Nat → Ty → SmfKind → Option Smf
  | 0, _, _ => none
  | fuel + 1, c, k =>
    match p.userDeclared c k with
    | some d => some { kind := k, prov := d.body.prov, constParam := d.constParam }
    | none =>
      let declared (k' : SmfKind) : Bool := (p.userDeclared c k').isSome
      let subConst (k' : SmfKind) : Bool :=
        (p.classSubobjects c).all fun m => ((p.specialWithin fuel m k').map (·.constParam)).getD true
      match k with
      | .defaultCtor =>
        if p.userDeclaredCtor c then none else some { kind := k, prov := .defaulted }
      | .copyCtor =>
        let suppressed := declared .moveCtor || declared .moveAssign
        some { kind := k, prov := if suppressed then .deleted else .defaulted
               constParam := subConst .copyCtor }
      | .moveCtor =>
        if declared .copyCtor || declared .copyAssign || declared .moveAssign || declared .dtor then none
        else some { kind := k, prov := .defaulted, constParam := false }
      | .copyAssign =>
        let suppressed := declared .moveCtor || declared .moveAssign
        some { kind := k, prov := if suppressed then .deleted else .defaulted
               constParam := subConst .copyAssign }
      | .moveAssign =>
        if declared .copyCtor || declared .moveCtor || declared .copyAssign || declared .dtor then none
        else some { kind := k, prov := .defaulted, constParam := false }
      | .dtor => some { kind := k, prov := .defaulted }

/-- The special member function of a kind that a class has, if any. -/
def special (p : Program) (c : Ty) (k : SmfKind) : Option Smf := p.specialWithin p.length c k

/-! ## Resolution over a class's constructors and assignment operators -/

/-- The facts the candidate lists consult: which special member a class
has, and whether a defaulted one is defined as deleted. -/
structure Facts where
  special : Ty → SmfKind → Option Smf
  deleted : Ty → SmfKind → Bool

/-- Is the special member deleted: absent, deleted on declaration, or
defaulted and defined as deleted? -/
def Facts.isDeleted (f : Facts) (c : Ty) (k : SmfKind) : Bool :=
  match f.special c k with
  | none => true
  | some s => s.prov == .deleted || (s.prov == .defaulted && f.deleted c k)

/-- The constructors of class `c` that overload resolution considers for
an initialization: its special constructors, a defaulted move
constructor that is defined as deleted left out ([class.copy.ctor]/10),
and its converting constructors, the explicit ones for
direct-initialization only. Each is numbered, and a special one carries
its kind. -/
@[std rule "class.copy.ctor#10" "over.match.ctor#1"]
def ctorCandidates (f : Facts) (p : Program) (init : Init) (c : Ty) : List (Candidate × Option SmfKind) :=
  let specials := [SmfKind.defaultCtor, .copyCtor, .moveCtor].filterMap fun k =>
    match f.special c k with
    | none => none
    | some s =>
      if k == .moveCtor && s.prov == .defaulted && f.deleted c k then none
      else some (s.params c, some k)
  let convs := (p.conversionsOf c).filterMap fun
    | conv@(.constructor param _) =>
      if (copyMoveForm c conv).isSome || !conv.candidate init then none else some ([param], none)
    | _ => none
  (specials ++ convs).zipIdx.map fun ((ps, k), i) => ({ index := i, params := ps }, k)

/-- The assignment operators of class `c`: its copy and move assignment,
a defaulted move assignment that is defined as deleted left out
([class.copy.assign]/7). -/
@[std rule "class.copy.assign#7"]
def assignCandidates (f : Facts) (c : Ty) : List (Candidate × Option SmfKind) :=
  ([SmfKind.copyAssign, .moveAssign].filterMap fun k =>
    match f.special c k with
    | none => none
    | some s =>
      if k == .moveAssign && s.prov == .defaulted && f.deleted c k then none
      else some (s.params c, some k)).zipIdx.map fun ((ps, k), i) => ({ index := i, params := ps }, k)

/-- Overload resolution over numbered candidates with the program's
ranking: the viable ones, then the best, by the rules of a call. -/
def resolveAmong (p : Program) (cands : List (Candidate × Option SmfKind)) (args : List CallArg) :
    Resolution (Candidate × Option SmfKind) :=
  match viable p.ranking (cands.map (·.1)) args with
  | .soft r | .hard r => .illFormed r
  | .ok vs =>
    match bestViable p.ranking (fun _ _ => false) vs with
    | .selected c =>
      match cands.find? (·.1.index == c.index) with
      | some x => .selected x
      | none => .noMatch
    | .noMatch => .noMatch
    | .ambiguous cs => .ambiguous (cands.filter fun x => cs.any (·.index == x.1.index))
    | .illFormed r => .illFormed r

/-- Overload resolution results in a usable candidate: it succeeds, and
the selected candidate is not deleted. Every special member and
converting constructor of the fragment is accessible. -/
@[std rule "over.match.general#4"]
def usable (f : Facts) (c : Ty) : Resolution (Candidate × Option SmfKind) → Bool
  | .selected (_, some k) => !f.isDeleted c k
  | .selected (_, none) => true
  | _ => false

/-- Resolution to find `c`'s constructor for the arguments. -/
def resolveCtor (f : Facts) (p : Program) (init : Init) (c : Ty) (args : List CallArg) :
    Resolution (Candidate × Option SmfKind) :=
  p.resolveAmong (ctorCandidates f p init c) args

/-- Resolution to find `c`'s assignment operator for the argument. -/
def resolveAssign (f : Facts) (p : Program) (c : Ty) (arg : CallArg) :
    Resolution (Candidate × Option SmfKind) :=
  p.resolveAmong (assignCandidates f c) [arg]

/-- The argument that copying or moving a subobject of type `t` supplies
to its class's constructor or assignment: an lvalue of `t`, `const` when
the enclosing member's parameter is a reference to `const`, for a copy;
an xvalue of `t` for a move. -/
def subobjectArg (t : Ty) (constParam : Bool) (move : Bool) : CallArg :=
  let m := t.stripConst
  let isConst := t matches .const _
  if move then { ty := if isConst then .const m else m, lvalue := false }
  else { ty := if constParam || isConst then .const m else m, lvalue := true }

/-! ## Defined as deleted -/

/-- A type is const-default-constructible within `fuel`: default-
initialization would invoke a user-provided constructor, or it is a
class each of whose members has a default member initializer or is
const-default-constructible and each of whose bases is. No scalar type of
the fragment is. -/
@[std rule "dcl.init.general#7"]
def constDefaultConstructibleWithin (p : Program) : Nat → Ty → Bool
  | 0, _ => false
  | fuel + 1, t =>
    let c := t.stripConst
    if !c.isClass then false
    else
      match p.userDeclared c .defaultCtor with
      | some d => d.body == .userProvided
      | none =>
        (p.membersOf c).all (fun m => m.init || p.constDefaultConstructibleWithin fuel m.ty) &&
        (p.directBases c).all (p.constDefaultConstructibleWithin fuel)

/-- A defaulted special member function of class `c` of kind `k` is
defined as deleted, within `fuel`: the bullets of [class.default.ctor]/2,
[class.copy.ctor]/10, [class.copy.assign]/7 and [class.dtor]/7 on the
fragment, each about a member's type or about resolution over a
subobject's class to find its corresponding special member. -/
@[std rule "class.default.ctor#2" "class.copy.ctor#10" "class.copy.assign#7" "class.dtor#7"]
def deletedWithin (p : Program) : Nat → Ty → SmfKind → Bool
  | 0, _, _ => false
  | fuel + 1, c, k =>
    let f : Facts := { special := p.specialWithin fuel, deleted := fun m k' => p.deletedWithin fuel m k' }
    let members := p.membersOf c
    let subs := p.subobjectsOf c
    let classSub (t : Ty) : Bool := t.stripConst.isClass
    let dtorDeleted : Bool := (p.classSubobjects c).any fun m => f.isDeleted m .dtor
    let constParam := ((p.specialWithin (fuel + 1) c k).map (·.constParam)).getD true
    match k with
    | .defaultCtor =>
      members.any (fun m => m.ty.isReference && !m.init) ||
      members.any (fun m => m.ty.isConst && !m.init && !p.constDefaultConstructibleWithin fuel m.ty) ||
      (members.any fun m => classSub m.ty && !m.init &&
        !usable f m.ty.stripConst (resolveCtor f p .direct m.ty.stripConst [])) ||
      ((p.directBases c).any fun b => !usable f b (resolveCtor f p .direct b [])) ||
      dtorDeleted
    | .copyCtor | .moveCtor =>
      (subs.any fun t => classSub t &&
        !usable f t.stripConst (resolveCtor f p .direct t.stripConst
          [subobjectArg t constParam (k == .moveCtor)])) ||
      dtorDeleted ||
      (k == .copyCtor && members.any (·.ty.isRvalueReference))
    | .copyAssign | .moveAssign =>
      members.any (fun m => m.ty.isConst && !m.ty.stripConst.isClass) ||
      members.any (·.ty.isReference) ||
      (subs.any fun t => classSub t &&
        ((t matches .const _) ||
          !usable f t.stripConst (resolveAssign f p t.stripConst
            (subobjectArg t constParam (k == .moveAssign)))))
    | .dtor => dtorDeleted

/-- The facts at a fuel: what `specialWithin` and `deletedWithin` say. -/
def factsWithin (p : Program) (fuel : Nat) : Facts :=
  { special := p.specialWithin fuel, deleted := p.deletedWithin fuel }

/-- The facts of the program: its special members and their deletion. -/
def facts (p : Program) : Facts := p.factsWithin p.length

/-- Is a defaulted special member of a class defined as deleted? -/
def deleted (p : Program) (c : Ty) (k : SmfKind) : Bool := p.deletedWithin p.length c k

/-- Is the class's special member of a kind deleted: absent, deleted on
its declaration, or defaulted and defined as deleted? -/
def isDeleted (p : Program) (c : Ty) (k : SmfKind) : Bool := p.facts.isDeleted c k

/-- An eligible special member function: one the class has, not deleted.
The fragment's special members carry no constraints, so the other two
conditions of [special]/6 hold. -/
@[std rule "special#6"]
def eligible (p : Program) (c : Ty) (k : SmfKind) : Bool :=
  (p.special c k).isSome && !p.isDeleted c k

/-! ## Trivial -/

/-- A special member function of class `c` of kind `k` is trivial, within
`fuel`: not user-provided, and, with no virtual functions or bases in the
fragment, the corresponding member selected for each subobject of class
type is a special member of that class and trivial; a default
constructor also needs no default member initializer. -/
@[std rule "class.default.ctor#3" "class.copy.ctor#12" "class.copy.assign#9" "class.dtor#8"]
def trivialWithin (p : Program) : Nat → Ty → SmfKind → Bool
  | 0, _, _ => false
  | fuel + 1, c, k =>
    match p.specialWithin (fuel + 1) c k with
    | none => false
    | some s =>
      let f := p.factsWithin fuel
      let classSub (t : Ty) : Bool := t.stripConst.isClass
      s.prov != .userProvided &&
      match k with
      | .defaultCtor =>
        (p.membersOf c).all (!·.init) &&
        (p.classSubobjects c).all fun m => p.trivialWithin fuel m .defaultCtor
      | .copyCtor | .moveCtor =>
        (p.subobjectsOf c).all fun t => !classSub t ||
          match resolveCtor f p .direct t.stripConst [subobjectArg t s.constParam (k == .moveCtor)] with
          | .selected (_, some k') => p.trivialWithin fuel t.stripConst k'
          | _ => false
      | .copyAssign | .moveAssign =>
        (p.subobjectsOf c).all fun t => !classSub t ||
          match resolveAssign f p t.stripConst (subobjectArg t s.constParam (k == .moveAssign)) with
          | .selected (_, some k') => p.trivialWithin fuel t.stripConst k'
          | _ => false
      | .dtor => (p.classSubobjects c).all fun m => p.trivialWithin fuel m .dtor

/-- Is the class's special member of a kind trivial? -/
def trivial (p : Program) (c : Ty) (k : SmfKind) : Bool := p.trivialWithin p.length c k

/-! ## The call's copy-initialization of a parameter -/

/-- Resolution to find the constructor that copy-initializes an object of
class `c` from the argument, among all of `c`'s constructors. -/
def copyInit (p : Program) (c : Ty) (a : CallArg) : Resolution (Candidate × Option SmfKind) :=
  resolveCtor p.facts p .copy c [a]

/-- Is copy-initializing a parameter of type `t` from the argument usable:
when `t` is a class type passed by value and the argument is of that
class or one derived from it, the constructor resolution selects is not
deleted; any other parameter is initialized by its conversion sequence,
which the ranking has already formed. A deleted selected constructor
makes the call ill-formed ([dcl.fct.def.delete]/2). -/
@[std rule "over.match.general#4" "dcl.fct.def.delete#2"]
def copyInitUsable (p : Program) (a : CallArg) (t : Ty) : Bool :=
  if t.isRef || !t.stripConst.isClass || !p.related a t then true
  else usable p.facts t.stripConst (p.copyInit t.stripConst a)

/-! ## Value and reference nature -/

/-- A class has value nature when every special member it has is
defaulted and not deleted: it is constructed, copied, moved, assigned and
destroyed by the rules alone. The author's name for it is data. -/
def valueNature (p : Program) (c : Ty) : Bool :=
  [SmfKind.defaultCtor, .copyCtor, .moveCtor, .copyAssign, .moveAssign, .dtor].all fun k =>
    match p.special c k with
    | some s => s.prov == .defaulted && !p.deleted c k
    | none => false

/-- A class has a reference member, through class-typed members and
bases likewise: a member of reference type or of `const` non-class type.
The author's name for the nature it gives the class is codata. -/
def referenceMemberWithin (p : Program) : Nat → Ty → Bool
  | 0, _ => false
  | fuel + 1, c =>
    (p.membersOf c).any (fun m => m.ty.isReference || (m.ty.isConst && !m.ty.stripConst.isClass)) ||
    (p.classSubobjects c).any (p.referenceMemberWithin fuel)

def referenceMember (p : Program) (c : Ty) : Bool := p.referenceMemberWithin p.length c

/-- A class that declares no special member, no conversion, no default
member initializer and no base: a flat class, whose special members are
all implicit. -/
def flatClass (p : Program) (c : Ty) : Bool :=
  (p.specialDecls c).isEmpty && (p.conversionsOf c).isEmpty && (p.directBases c).isEmpty &&
    (p.membersOf c).all fun m => !m.init && !m.ty.stripConst.isClass

end Program

/-- Each defaulted special member of a flat class: the rules declare all
six, the copy ones with a reference to `const`. -/
theorem special_flat (p : Program) (c : Ty) (hc : p.flatClass c = true) (hl : 0 < p.length)
    (k : SmfKind) : p.special c k = some { kind := k, prov := .defaulted, constParam := k.isCtor && k != .moveCtor || k == .copyAssign || k == .dtor } := by
  simp only [Program.flatClass, Bool.and_eq_true, List.isEmpty_iff] at hc
  obtain ⟨⟨⟨hs, hconv⟩, hb⟩, hm⟩ := hc
  have hud : ∀ k', p.userDeclared c k' = none := by
    intro k'; simp [Program.userDeclared, hs, hconv]
  have hudc : p.userDeclaredCtor c = false := by simp [Program.userDeclaredCtor, hs, hconv]
  have hcs : p.classSubobjects c = [] := by
    simp only [Program.classSubobjects, Program.subobjectsOf, hb, List.append_nil, List.filterMap_map]
    simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hm
    rw [List.filterMap_eq_nil_iff]
    intro m hmem
    simp [Function.comp, (hm m hmem).2]
  unfold Program.special
  obtain ⟨n, hn⟩ : ∃ n, p.length = n + 1 := ⟨p.length - 1, by omega⟩
  rw [hn]
  cases k <;> simp [Program.specialWithin, hud, hudc, hcs, SmfKind.isCtor]

/-- No non-class type of the fragment is const-default-constructible. -/
theorem constDefaultConstructibleWithin_nonclass (p : Program) (n : Nat) (t : Ty)
    (h : t.stripConst.isClass = false) : p.constDefaultConstructibleWithin n t = false := by
  cases n with
  | zero => rfl
  | succ n => simp [Program.constDefaultConstructibleWithin, h]

/-- A flat class's defaulted special members are defined as deleted
exactly by its reference and `const` members: the default constructor
and the two assignments by a reference or `const` member, the copy
constructor by an rvalue reference member, the move constructor and the
destructor never. This is the value nature of a flat class, decided by
its members alone. -/
theorem deleted_flat (p : Program) (c : Ty) (hc : p.flatClass c = true) (hl : 0 < p.length) :
    (p.deleted c .defaultCtor = (p.membersOf c).any (fun m => m.ty.isReference || m.ty.isConst)) ∧
    (p.deleted c .copyCtor = (p.membersOf c).any (·.ty.isRvalueReference)) ∧
    (p.deleted c .moveCtor = false) ∧
    (p.deleted c .copyAssign = (p.membersOf c).any (fun m => m.ty.isReference || m.ty.isConst)) ∧
    (p.deleted c .moveAssign = (p.membersOf c).any (fun m => m.ty.isReference || m.ty.isConst)) ∧
    (p.deleted c .dtor = false) := by
  simp only [Program.flatClass, Bool.and_eq_true, List.isEmpty_iff] at hc
  obtain ⟨⟨⟨hs, hconv⟩, hb⟩, hm⟩ := hc
  simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hm
  have hcs : p.classSubobjects c = [] := by
    simp only [Program.classSubobjects, Program.subobjectsOf, hb, List.append_nil, List.filterMap_map]
    rw [List.filterMap_eq_nil_iff]
    intro m hmem
    simp [Function.comp, (hm m hmem).2]
  have hsub : ∀ t ∈ p.subobjectsOf c, t.stripConst.isClass = false := by
    intro t ht
    simp only [Program.subobjectsOf, hb, List.append_nil, List.mem_map] at ht
    obtain ⟨m, hmem, rfl⟩ := ht
    exact (hm m hmem).2
  have hsubs : ∀ g : Ty → Bool, ((p.subobjectsOf c).any fun t => t.stripConst.isClass && g t) = false :=
    fun g => List.any_eq_false.mpr fun t ht => by simp [hsub t ht]
  unfold Program.deleted
  obtain ⟨n, hn⟩ : ∃ n, p.length = n + 1 := ⟨p.length - 1, by omega⟩
  rw [hn]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- default constructor
    simp only [Program.deletedWithin, hcs, hb, List.any_nil, Bool.or_false]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true']
    constructor
    · rintro ((⟨m, hmem, h⟩ | ⟨m, hmem, h⟩) | ⟨m, hmem, h⟩)
      · exact ⟨m, hmem, Or.inl h.1⟩
      · exact ⟨m, hmem, Or.inr h.1.1⟩
      · exact absurd h.1.1 (by simp [(hm m hmem).2])
    · rintro ⟨m, hmem, h | h⟩
      · exact Or.inl (Or.inl ⟨m, hmem, h, (hm m hmem).1⟩)
      · exact Or.inl (Or.inr ⟨m, hmem, ⟨h, (hm m hmem).1⟩,
          constDefaultConstructibleWithin_nonclass p n m.ty (hm m hmem).2⟩)
  · -- copy constructor
    simp only [Program.deletedWithin, hcs, List.any_nil, Bool.or_false, hsubs, Bool.false_or,
      beq_self_eq_true, Bool.true_and]
  · -- move constructor
    simp only [Program.deletedWithin, hcs, List.any_nil, Bool.or_false, hsubs, Bool.false_or]
    rfl
  · -- copy assignment
    simp only [Program.deletedWithin]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true']
    constructor
    · rintro ((⟨m, hmem, h⟩ | ⟨m, hmem, h⟩) | ⟨t, ht, h⟩)
      · exact ⟨m, hmem, Or.inr h.1⟩
      · exact ⟨m, hmem, Or.inl h⟩
      · exact absurd h.1 (by simp [hsub t ht])
    · rintro ⟨m, hmem, h | h⟩
      · exact Or.inl (Or.inr ⟨m, hmem, h⟩)
      · exact Or.inl (Or.inl ⟨m, hmem, h, (hm m hmem).2⟩)
  · -- move assignment
    simp only [Program.deletedWithin]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true']
    constructor
    · rintro ((⟨m, hmem, h⟩ | ⟨m, hmem, h⟩) | ⟨t, ht, h⟩)
      · exact ⟨m, hmem, Or.inr h.1⟩
      · exact ⟨m, hmem, Or.inl h⟩
      · exact absurd h.1 (by simp [hsub t ht])
    · rintro ⟨m, hmem, h | h⟩
      · exact Or.inl (Or.inr ⟨m, hmem, h⟩)
      · exact Or.inl (Or.inl ⟨m, hmem, h, (hm m hmem).2⟩)
  · -- destructor
    simp [Program.deletedWithin, hcs]

/-- A flat class has value nature exactly when no member is of reference
type or `const` type: the author's data and codata, decided by the
members alone. The rvalue reference member that deletes the copy
constructor is a reference member, so it adds no case. -/
theorem value_nature_flat (p : Program) (c : Ty) (hc : p.flatClass c = true) (hl : 0 < p.length) :
    p.valueNature c = !(p.membersOf c).any (fun m => m.ty.isReference || m.ty.isConst) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := deleted_flat p c hc hl
  have hBA : (p.membersOf c).any (·.ty.isRvalueReference) = true →
      (p.membersOf c).any (fun m => m.ty.isReference || m.ty.isConst) = true := by
    simp only [List.any_eq_true]
    rintro ⟨m, hmem, h⟩
    exact ⟨m, hmem, by simp [Ty.isReference, h]⟩
  simp only [Program.valueNature, List.all_cons, List.all_nil, special_flat p c hc hl, h0, h1, h2, h3,
    h4, h5, beq_self_eq_true, Bool.true_and, Bool.not_false, Bool.and_true]
  cases hA : (p.membersOf c).any (fun m => m.ty.isReference || m.ty.isConst) <;>
    cases hB : (p.membersOf c).any (·.ty.isRvalueReference) <;> simp_all

/-- A pointer member deletes nothing: a flat class whose members are all
pointers has value nature. The type system says a pointer is data; what
it points to is outside the fragment (`decisions.md#value-nature`). -/
theorem pointer_member_keeps_value_nature (p : Program) (c : Ty) (hc : p.flatClass c = true)
    (hl : 0 < p.length) (hptr : ∀ m ∈ p.membersOf c, m.ty matches .ptr _) :
    p.valueNature c = true := by
  rw [value_nature_flat p c hc hl, Bool.not_eq_true', List.any_eq_false]
  intro m hmem
  have := hptr m hmem
  cases hm : m.ty <;> simp_all [Ty.isReference, Ty.isLvalueReference, Ty.isRvalueReference, Ty.isConst]

end Overload
