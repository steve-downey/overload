-- Overload/Special.lean                                              -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Ranking
import Overload.Types
import Overload.Virtual

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
(`decisions.md#value-nature`): `value_nature_iff` for every class whose
special members are the rules' own, on seven lemmas about what overload
resolution over a class's implicit members selects.
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

/-- The special member function of kind `k` the rules declare for a class
that declares none: defaulted, its parameter a reference to `const`
except for the move members. -/
def Smf.implicit (k : SmfKind) : Smf :=
  { kind := k, prov := .defaulted, constParam := k != .moveCtor && k != .moveAssign }

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

/-- Is a user-defined conversion potentially throwing: its specifier says
so, or it has none, since a converting constructor or conversion function
is user-provided and a declaration without a noexcept-specifier is
potentially throwing. -/
@[std rule "except.spec#4"]
def UserConv.throwing (c : UserConv) : Bool := c.noexcept != some true

namespace Program

/-- A converting constructor whose parameter makes it a copy or move
constructor of its class: `X&` or `const X&`, `X&&` or `const X&&`. It is
user-declared and user-provided. -/
@[std rule "class.copy.ctor#1" "class.copy.ctor#2"]
def copyMoveForm (c : Ty) : UserConv → Option SmfDecl
  | .constructor (.lref t) _ _ =>
    if t == c then some { kind := .copyCtor, constParam := false }
    else if t == .const c then some { kind := .copyCtor } else none
  | .constructor (.rref t) _ _ =>
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
fragment has a virtual base, so the abstract classes' exception for
them never applies. -/
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
    | conv@(.constructor param _ _) =>
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
`fuel`: the class is not polymorphic, so it has no virtual functions and
its destructor is not virtual, with no virtual bases in the fragment;
the member is not user-provided; the corresponding member selected for
each subobject of class type is a special member of that class and
trivial; and a default constructor needs no default member initializer. -/
@[std rule "class.default.ctor#3" "class.copy.ctor#12" "class.copy.assign#9" "class.dtor#8"]
def trivialWithin (p : Program) : Nat → Ty → SmfKind → Bool
  | 0, _, _ => false
  | fuel + 1, c, k =>
    match p.specialWithin (fuel + 1) c k with
    | none => false
    | some s =>
      let f := p.factsWithin fuel
      let classSub (t : Ty) : Bool := t.stripConst.isClass
      !p.polymorphic c && s.prov != .userProvided &&
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

/-! ## Exception specifications -/

/-- Is the converting constructor of class `c` with these parameters
potentially throwing? Resolution names a converting constructor by its
parameter list; one the class does not declare is taken as potentially
throwing. -/
@[std rule "except.spec#4"]
def convThrowing (p : Program) (c : Ty) (params : List Ty) : Bool :=
  match (p.conversionsOf c).find? fun | .constructor param _ _ => [param] == params | _ => false with
  | some conv => conv.throwing
  | none => true

/-- Is the constructor a resolution selected potentially throwing: a
special member by `throwing`, a converting constructor by its specifier;
a resolution that selects nothing invokes nothing. -/
@[std rule "except.spec#6"]
def selectedCtorThrowing (p : Program) (throwing : Ty → SmfKind → Bool) (c : Ty) :
    Resolution (Candidate × Option SmfKind) → Bool
  | .selected (_, some k) => throwing c k
  | .selected (cand, none) => p.convThrowing c cand.params
  | _ => false

/-- Is the special member of class `c` of kind `k` potentially throwing,
within `fuel`: a user-declared member's specifier decides; a
user-provided one without a specifier is potentially throwing, unless it
is a destructor; a destructor or a defaulted member without a specifier
has the implicit exception specification, potentially throwing exactly
when a constructor, assignment or destructor the implicit definition
invokes on a potentially constructed subobject is, or, for a default
constructor, a default member initializer is. The subobjects' members
are found by the same resolution as their deletion. -/
@[std rule "except.spec#4" "except.spec#7" "except.spec#8" "except.spec#9"]
def throwingWithin (p : Program) : Nat → Ty → SmfKind → Bool
  | 0, _, _ => false
  | fuel + 1, c, k =>
    let implicit : Bool :=
      let f := p.factsWithin fuel
      let sub (m : Ty) (k' : SmfKind) : Bool := p.throwingWithin fuel m k'
      let constParam := ((p.specialWithin (fuel + 1) c k).map (·.constParam)).getD true
      let classSub (t : Ty) : Bool := t.stripConst.isClass
      let ctorThrows (t : Ty) (args : List CallArg) : Bool :=
        p.selectedCtorThrowing sub t.stripConst (resolveCtor f p .direct t.stripConst args)
      match k with
      | .defaultCtor =>
        ((p.membersOf c).any fun m => (m.init && m.throwingInit) || (classSub m.ty && ctorThrows m.ty [])) ||
        ((p.directBases c).any fun b => ctorThrows b [])
      | .copyCtor | .moveCtor =>
        (p.subobjectsOf c).any fun t => classSub t &&
          ctorThrows t [subobjectArg t constParam (k == .moveCtor)]
      | .copyAssign | .moveAssign =>
        (p.subobjectsOf c).any fun t => classSub t &&
          match resolveAssign f p t.stripConst (subobjectArg t constParam (k == .moveAssign)) with
          | .selected (_, some k') => sub t.stripConst k'
          | _ => false
      | .dtor => (p.classSubobjects c).any fun m => sub m .dtor
    match p.userDeclared c k with
    | some d =>
      match d.noexcept with
      | some b => !b
      | none => if d.body == .userProvided && k != .dtor then true else implicit
    | none => implicit

/-- Is the class's special member of a kind potentially throwing? -/
def throwing (p : Program) (c : Ty) (k : SmfKind) : Bool := p.throwingWithin p.length c k

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

/-- Is the initialization of a parameter of type `t` from the argument
potentially throwing: a user-defined conversion that is, or, for a
by-value class parameter initialized by a standard conversion sequence,
the constructor its copy-initialization selects. A standard sequence
to a scalar or a reference invokes no function. -/
@[std rule "except.spec#6"]
def initThrowing (p : Program) (a : CallArg) (t : Ty) : Bool :=
  match p.ics .copy a t with
  | some (.userDefined _ (_, conv) _) => conv.throwing
  | some (.standard _) =>
    if !t.isRef && t.stripConst.isClass then
      p.selectedCtorThrowing p.throwing t.stripConst (p.copyInit t.stripConst a)
    else false
  | _ => false

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
bases likewise: a potentially constructed subobject of reference type or
of `const` type. A `const` member of class type counts, since it deletes
the assignment operators as a `const` scalar does; a base is never a
reference or `const`, so the subobjects serve for the members. The
author's name for the nature it gives the class is codata. -/
def referenceMemberWithin (p : Program) : Nat → Ty → Bool
  | 0, _ => false
  | fuel + 1, c =>
    (p.subobjectsOf c).any (fun t => t.isReference || t.isConst) ||
    (p.classSubobjects c).any (p.referenceMemberWithin fuel)

def referenceMember (p : Program) (c : Ty) : Bool := p.referenceMemberWithin p.length c

/-- The declarations of a class are well-formed as far as the special
member rules read them: each direct base is a class type, not `const`,
and each member's type carries one top-level `const` at most. -/
def subobjectsWellFormed (p : Program) (c : Ty) : Bool :=
  (p.directBases c).all (fun b => b.isClass && !b.isConst) &&
    (p.membersOf c).all fun m => !m.ty.stripConst.isConst

/-- A class whose special member functions are all the rules' own, within
`fuel` steps of subobject nesting: it declares no special member and no
conversion, its declarations are well-formed, and the class of each of
its class-typed subobjects is such a class likewise. -/
def implicitWithin (p : Program) : Nat → Ty → Bool
  | 0, _ => false
  | fuel + 1, c =>
    (p.specialDecls c).isEmpty && (p.conversionsOf c).isEmpty && p.subobjectsWellFormed c &&
      (p.classSubobjects c).all (p.implicitWithin fuel)

/-- A class whose special member functions, and those of every class
reachable through its subobjects, are implicitly declared. -/
def implicitClass (p : Program) (c : Ty) : Bool := p.implicitWithin p.length c

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

/-- A converting constructor of copy or move form is a copy or move
constructor, never a special member of another kind. -/
theorem copyMoveForm_kind (c : Ty) (conv : UserConv) (s : SmfDecl)
    (h : Program.copyMoveForm c conv = some s) : s.kind = .copyCtor ∨ s.kind = .moveCtor := by
  unfold Program.copyMoveForm at h
  split at h <;> (try simp only [reduceCtorEq] at h)
  all_goals
    split at h <;> (try split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> simp

/-- A destructor declared without a noexcept-specifier has the exception
specification it would have had implicitly declared: potentially throwing
exactly when a potentially constructed subobject's destructor is. -/
@[std note "class.dtor#6"]
theorem dtor_without_specifier_implicit (p : Program) (fuel : Nat) (c : Ty) (d : SmfDecl)
    (hud : p.userDeclared c .dtor = some d) (hne : d.noexcept = none) :
    p.throwingWithin (fuel + 1) c .dtor =
      (p.classSubobjects c).any fun m => p.throwingWithin fuel m .dtor := by
  simp [Program.throwingWithin, hud, hne]

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

/-! ## A class whose special members are the rules' own -/

/-- A type that is not `const` is its own `stripConst`. -/
theorem stripConst_of_not_const (t : Ty) (h : t.isConst = false) : t.stripConst = t := by
  cases t <;> simp_all [Ty.isConst, Ty.stripConst]

/-- A class type is not a reference, so it is its own `referred`. -/
theorem referred_of_class (t : Ty) (h : t.isClass = true) : t.referred = t := by
  cases t <;> simp_all [Ty.isClass, Ty.stripConst, Ty.referred]

/-- A class type is not a reference. -/
theorem not_reference_of_class (t : Ty) (h : t.isClass = true) : t.isReference = false := by
  cases t <;> simp_all [Ty.isClass, Ty.stripConst, Ty.isReference, Ty.isLvalueReference,
    Ty.isRvalueReference]

/-- The conjuncts of `implicitWithin` at a positive fuel. -/
theorem implicitWithin_succ (p : Program) (fuel : Nat) (c : Ty)
    (h : p.implicitWithin (fuel + 1) c = true) :
    p.specialDecls c = [] ∧ p.conversionsOf c = [] ∧ p.subobjectsWellFormed c = true ∧
      ∀ m ∈ p.classSubobjects c, p.implicitWithin fuel m = true := by
  simp only [Program.implicitWithin, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- A class that is implicit at any fuel declares no conversion. -/
theorem implicitWithin_conversions (p : Program) (fuel : Nat) (c : Ty)
    (h : p.implicitWithin fuel c = true) : p.conversionsOf c = [] := by
  cases fuel with
  | zero => simp [Program.implicitWithin] at h
  | succ n => exact (implicitWithin_succ p n c h).2.1

/-- The special members of a class whose special members are the rules'
own: all six, defaulted, the copy members with a reference to `const`
since every subobject's are. -/
theorem specialWithin_implicit (p : Program) :
    ∀ fuel c, p.implicitWithin fuel c = true → ∀ k, p.specialWithin fuel c k = some (Smf.implicit k) := by
  intro fuel
  induction fuel with
  | zero => intro c h; simp [Program.implicitWithin] at h
  | succ n ih =>
    intro c h k
    obtain ⟨hs, hconv, -, hsub⟩ := implicitWithin_succ p n c h
    have hud : ∀ k', p.userDeclared c k' = none := by
      intro k'; simp [Program.userDeclared, hs, hconv]
    have hudc : p.userDeclaredCtor c = false := by simp [Program.userDeclaredCtor, hs, hconv]
    have hcc : ((p.classSubobjects c).all fun m =>
        ((p.specialWithin n m .copyCtor).map (·.constParam)).getD true) = true :=
      List.all_eq_true.mpr fun m hm => by simp [ih m (hsub m hm) .copyCtor, Smf.implicit]
    have hca : ((p.classSubobjects c).all fun m =>
        ((p.specialWithin n m .copyAssign).map (·.constParam)).getD true) = true :=
      List.all_eq_true.mpr fun m hm => by simp [ih m (hsub m hm) .copyAssign, Smf.implicit]
    cases k <;> simp [Program.specialWithin, hud, hudc, hcc, hca, Smf.implicit]

/-! ### Resolution over the implicit members of a class

The lemmas take the facts of a class `M` whose special members are the
rules' own, and say which member overload resolution selects for each
argument a subobject supplies: the default constructor for no argument;
the copy member for an lvalue; the move member for an rvalue of the class,
since binding an rvalue reference to an rvalue is the better conversion
([over.ics.rank]/3); and the copy member for an rvalue of `const` class,
or when the defaulted move member is defined as deleted and so is not a
candidate ([class.copy.ctor]/10, [class.copy.assign]/7). -/

/-- The facts of a class whose special members are the rules' own. -/
def Program.Facts.implicitFor (f : Program.Facts) (M : Ty) : Prop := ∀ k, f.special M k = some (Smf.implicit k)

section ResolutionLemmas

attribute [local simp] Program.resolveAmong viable viable.go conversions arityOk bestViable
  betterFunction Program.ranking Program.ics Program.standardIcs Program.canBind
  Program.referenceCompatible Program.baseConv Program.related Program.betterIcs Program.better
  lexBetter Program.tiers Program.byRank Program.byRvalueBinding Program.byQualification
  ConvRank.better Ty.referred Ty.stripConst Ty.isClass Smf.implicit Smf.params

variable (f : Program.Facts) (p : Program) (M : Ty) (hM : M.isClass = true) (hMc : M.isConst = false)
  (hconv : p.conversionsOf M = []) (hf : f.implicitFor M)
include hconv hf

omit hconv in
/-- The three constructors the facts give the class. -/
theorem Facts.ctors : f.special M .defaultCtor = some (Smf.implicit .defaultCtor) ∧
    f.special M .copyCtor = some (Smf.implicit .copyCtor) ∧
    f.special M .moveCtor = some (Smf.implicit .moveCtor) := ⟨hf _, hf _, hf _⟩

omit hconv in
/-- The two assignment operators the facts give the class. -/
theorem Facts.assigns : f.special M .copyAssign = some (Smf.implicit .copyAssign) ∧
    f.special M .moveAssign = some (Smf.implicit .moveAssign) := ⟨hf _, hf _⟩

/-- With no argument, the default constructor. -/
theorem resolveCtor_nullary :
    p.resolveCtor f .direct M [] = .selected ({ index := 0, params := [] }, some .defaultCtor) := by
  obtain ⟨h0, h1, h2⟩ := Facts.ctors f M hf
  unfold Program.resolveCtor Program.ctorCandidates
  cases hd : f.deleted M .moveCtor <;> simp [h0, h1, h2, hconv, hd]

include hM hMc

/-- With an lvalue of the class, `const` or not, the copy constructor:
the move constructor binds no lvalue. -/
theorem resolveCtor_lvalue (t : Ty) (ht : t = M ∨ t = .const M) :
    p.resolveCtor f .direct M [{ ty := t, lvalue := true }] =
      .selected ({ index := 1, params := [.lref (.const M)] }, some .copyCtor) := by
  obtain ⟨h0, h1, h2⟩ := Facts.ctors f M hf
  unfold Program.resolveCtor Program.ctorCandidates
  cases hd : f.deleted M .moveCtor <;> cases M <;> simp [Ty.isConst] at hM hMc <;>
    rcases ht with rfl | rfl <;> simp [h0, h1, h2, hconv, hd]

/-- With an rvalue of the class, the move constructor when it is a
candidate: it binds an rvalue reference to an rvalue, which is the better
conversion. -/
theorem resolveCtor_rvalue_move (hd : f.deleted M .moveCtor = false) :
    p.resolveCtor f .direct M [{ ty := M, lvalue := false }] =
      .selected ({ index := 2, params := [.rref M] }, some .moveCtor) := by
  obtain ⟨h0, h1, h2⟩ := Facts.ctors f M hf
  unfold Program.resolveCtor Program.ctorCandidates
  cases M <;> simp [Ty.isConst] at hM hMc <;> simp [h0, h1, h2, hconv, hd]

/-- With an rvalue of the `const` class, or when the defaulted move
constructor is defined as deleted and so is not a candidate, the copy
constructor. -/
theorem resolveCtor_rvalue_copy (t : Ty)
    (ht : t = M ∧ f.deleted M .moveCtor = true ∨ t = .const M) :
    p.resolveCtor f .direct M [{ ty := t, lvalue := false }] =
      .selected ({ index := 1, params := [.lref (.const M)] }, some .copyCtor) := by
  obtain ⟨h0, h1, h2⟩ := Facts.ctors f M hf
  unfold Program.resolveCtor Program.ctorCandidates
  rcases ht with ⟨rfl, hd⟩ | rfl
  · cases t <;> simp [Ty.isConst] at hM hMc <;> simp [h0, h1, h2, hconv, hd]
  · cases hd : f.deleted M .moveCtor <;> cases M <;> simp [Ty.isConst] at hM hMc <;>
      simp [h0, h1, h2, hconv, hd]

omit hconv in
/-- With an lvalue of the class, `const` or not, the copy assignment. -/
theorem resolveAssign_lvalue (t : Ty) (ht : t = M ∨ t = .const M) :
    p.resolveAssign f M { ty := t, lvalue := true } =
      .selected ({ index := 0, params := [.lref (.const M)] }, some .copyAssign) := by
  obtain ⟨h3, h4⟩ := Facts.assigns f M hf
  unfold Program.resolveAssign Program.assignCandidates
  cases hd : f.deleted M .moveAssign <;> cases M <;> simp [Ty.isConst] at hM hMc <;>
    rcases ht with rfl | rfl <;> simp [h3, h4, hd]

omit hconv in
/-- With an rvalue of the class, the move assignment when it is a
candidate. -/
theorem resolveAssign_rvalue_move (hd : f.deleted M .moveAssign = false) :
    p.resolveAssign f M { ty := M, lvalue := false } =
      .selected ({ index := 1, params := [.rref M] }, some .moveAssign) := by
  obtain ⟨h3, h4⟩ := Facts.assigns f M hf
  unfold Program.resolveAssign Program.assignCandidates
  cases M <;> simp [Ty.isConst] at hM hMc <;> simp [h3, h4, hd]

omit hconv in
/-- With an rvalue of the `const` class, or when the defaulted move
assignment is defined as deleted, the copy assignment. -/
theorem resolveAssign_rvalue_copy (t : Ty)
    (ht : t = M ∧ f.deleted M .moveAssign = true ∨ t = .const M) :
    p.resolveAssign f M { ty := t, lvalue := false } =
      .selected ({ index := 0, params := [.lref (.const M)] }, some .copyAssign) := by
  obtain ⟨h3, h4⟩ := Facts.assigns f M hf
  unfold Program.resolveAssign Program.assignCandidates
  rcases ht with ⟨rfl, hd⟩ | rfl
  · cases t <;> simp [Ty.isConst] at hM hMc <;> simp [h3, h4, hd]
  · cases hd : f.deleted M .moveAssign <;> cases M <;> simp [Ty.isConst] at hM hMc <;>
      simp [h3, h4, hd]

end ResolutionLemmas

/-! ### The deletion rules at a positive fuel, one kind at a time -/

namespace Program

/-- [class.dtor]/7 at a fuel: a subobject's deleted destructor. -/
theorem deletedWithin_dtor (p : Program) (n : Nat) (c : Ty) :
    p.deletedWithin (n + 1) c .dtor =
      (p.classSubobjects c).any fun m => (p.factsWithin n).isDeleted m .dtor := rfl

/-- [class.default.ctor]/2 at a fuel. -/
theorem deletedWithin_defaultCtor (p : Program) (n : Nat) (c : Ty) :
    p.deletedWithin (n + 1) c .defaultCtor =
      ((p.membersOf c).any (fun m => m.ty.isReference && !m.init) ||
       (p.membersOf c).any (fun m => m.ty.isConst && !m.init && !p.constDefaultConstructibleWithin n m.ty) ||
       ((p.membersOf c).any fun m => m.ty.stripConst.isClass && !m.init &&
         !usable (p.factsWithin n) m.ty.stripConst (resolveCtor (p.factsWithin n) p .direct m.ty.stripConst [])) ||
       ((p.directBases c).any fun b => !usable (p.factsWithin n) b (resolveCtor (p.factsWithin n) p .direct b [])) ||
       (p.classSubobjects c).any fun m => (p.factsWithin n).isDeleted m .dtor) := rfl

/-- [class.copy.ctor]/10 at a fuel, for the copy constructor. -/
theorem deletedWithin_copyCtor (p : Program) (n : Nat) (c : Ty) :
    p.deletedWithin (n + 1) c .copyCtor =
      (((p.subobjectsOf c).any fun t => t.stripConst.isClass &&
         !usable (p.factsWithin n) t.stripConst (resolveCtor (p.factsWithin n) p .direct t.stripConst
           [subobjectArg t (((p.specialWithin (n + 1) c .copyCtor).map (·.constParam)).getD true) false])) ||
       ((p.classSubobjects c).any fun m => (p.factsWithin n).isDeleted m .dtor) ||
       (p.membersOf c).any (·.ty.isRvalueReference)) := rfl

/-- [class.copy.ctor]/10 at a fuel, for the move constructor. -/
theorem deletedWithin_moveCtor (p : Program) (n : Nat) (c : Ty) :
    p.deletedWithin (n + 1) c .moveCtor =
      (((p.subobjectsOf c).any fun t => t.stripConst.isClass &&
         !usable (p.factsWithin n) t.stripConst (resolveCtor (p.factsWithin n) p .direct t.stripConst
           [subobjectArg t (((p.specialWithin (n + 1) c .moveCtor).map (·.constParam)).getD true) true])) ||
       (p.classSubobjects c).any fun m => (p.factsWithin n).isDeleted m .dtor) := by
  simp [Program.deletedWithin, Program.factsWithin]

/-- [class.copy.assign]/7 at a fuel, for the copy assignment. -/
theorem deletedWithin_copyAssign (p : Program) (n : Nat) (c : Ty) :
    p.deletedWithin (n + 1) c .copyAssign =
      ((p.membersOf c).any (fun m => m.ty.isConst && !m.ty.stripConst.isClass) ||
       (p.membersOf c).any (·.ty.isReference) ||
       (p.subobjectsOf c).any fun t => t.stripConst.isClass &&
         (t.isConst || !usable (p.factsWithin n) t.stripConst (resolveAssign (p.factsWithin n) p t.stripConst
           (subobjectArg t (((p.specialWithin (n + 1) c .copyAssign).map (·.constParam)).getD true) false)))) := rfl

/-- [class.copy.assign]/7 at a fuel, for the move assignment. -/
theorem deletedWithin_moveAssign (p : Program) (n : Nat) (c : Ty) :
    p.deletedWithin (n + 1) c .moveAssign =
      ((p.membersOf c).any (fun m => m.ty.isConst && !m.ty.stripConst.isClass) ||
       (p.membersOf c).any (·.ty.isReference) ||
       (p.subobjectsOf c).any fun t => t.stripConst.isClass &&
         (t.isConst || !usable (p.factsWithin n) t.stripConst (resolveAssign (p.factsWithin n) p t.stripConst
           (subobjectArg t (((p.specialWithin (n + 1) c .moveAssign).map (·.constParam)).getD true) true)))) := rfl

/-- The argument a copy supplies: an lvalue of the subobject's class,
`const` or not. -/
theorem subobjectArg_copy (t : Ty) (cp : Bool) :
    subobjectArg t cp false = { ty := t.stripConst, lvalue := true } ∨
    subobjectArg t cp false = { ty := .const t.stripConst, lvalue := true } := by
  unfold subobjectArg; cases cp <;> cases t <;> simp

/-- The argument a move supplies for a subobject that is not `const`: an
xvalue of its class. -/
theorem subobjectArg_move (t : Ty) (cp : Bool) (hc : t.isConst = false) :
    subobjectArg t cp true = { ty := t.stripConst, lvalue := false } := by
  unfold subobjectArg; cases t <;> simp_all [Ty.isConst]

/-- The argument a move supplies for a `const` subobject: an xvalue of
the `const` class. -/
theorem subobjectArg_move_const (t : Ty) (cp : Bool) (hc : t.isConst = true) :
    subobjectArg t cp true = { ty := .const t.stripConst, lvalue := false } := by
  unfold subobjectArg; cases t <;> simp_all [Ty.isConst]

/-- A member's type is a potentially constructed subobject. -/
theorem mem_subobjectsOf_of_member (p : Program) (c : Ty) (m : Member) (hm : m ∈ p.membersOf c) :
    m.ty ∈ p.subobjectsOf c := by
  simp only [subobjectsOf, List.mem_append, List.mem_map]; exact Or.inl ⟨m, hm, rfl⟩

/-- A direct base is a potentially constructed subobject. -/
theorem mem_subobjectsOf_of_base (p : Program) (c b : Ty) (hb : b ∈ p.directBases c) :
    b ∈ p.subobjectsOf c := by
  simp only [subobjectsOf, List.mem_append]; exact Or.inr hb

/-- A subobject of class type gives its class to `classSubobjects`. -/
theorem mem_classSubobjects (p : Program) (c t : Ty) (ht : t ∈ p.subobjectsOf c)
    (hc : t.stripConst.isClass = true) : t.stripConst ∈ p.classSubobjects c := by
  simp only [classSubobjects, List.mem_filterMap]
  exact ⟨t, ht, by simp [hc]⟩

/-- Some class subobject satisfies `g` exactly when some subobject of
class type has a class satisfying it. -/
theorem any_classSubobjects_iff (p : Program) (c : Ty) (g : Ty → Bool) :
    (p.classSubobjects c).any g = true ↔
      ∃ t ∈ p.subobjectsOf c, t.stripConst.isClass = true ∧ g t.stripConst = true := by
  simp only [List.any_eq_true, classSubobjects, List.mem_filterMap]
  constructor
  · rintro ⟨m, ⟨t, ht, hm⟩, hg⟩
    by_cases hc : t.stripConst.isClass = true
    · simp only [hc, ↓reduceIte, Option.some.injEq] at hm
      subst hm; exact ⟨t, ht, hc, hg⟩
    · simp [hc] at hm
  · rintro ⟨t, ht, hc, hg⟩
    exact ⟨t.stripConst, ⟨t, ht, by simp [hc]⟩, hg⟩

/-- Under `subobjectsWellFormed`, a subobject's class is not `const`. -/
theorem wellFormed_subobject (p : Program) (c t : Ty) (hw : p.subobjectsWellFormed c = true)
    (ht : t ∈ p.subobjectsOf c) : t.stripConst.isConst = false := by
  simp only [subobjectsWellFormed, Bool.and_eq_true, List.all_eq_true] at hw
  simp only [subobjectsOf, List.mem_append, List.mem_map] at ht
  rcases ht with ⟨m, hm, rfl⟩ | hb
  · simpa using hw.2 m hm
  · have := hw.1 t hb
    simp only [Bool.not_eq_true'] at this
    rw [stripConst_of_not_const t this.2]; exact this.2

/-- Under `subobjectsWellFormed`, a direct base is a class type that is
neither `const` nor a reference. -/
theorem wellFormed_base (p : Program) (c b : Ty) (hw : p.subobjectsWellFormed c = true)
    (hb : b ∈ p.directBases c) : b.isClass = true ∧ b.isConst = false ∧ b.isReference = false := by
  simp only [subobjectsWellFormed, Bool.and_eq_true, List.all_eq_true] at hw
  have := hw.1 b hb
  simp only [Bool.not_eq_true'] at this
  exact ⟨this.1, this.2, not_reference_of_class b this.1⟩

/-- Resolution results in a usable candidate exactly when the special
member it selects is not deleted. -/
theorem usable_selected (f : Facts) (c : Ty) (x : Candidate) (k : SmfKind) :
    usable f c (.selected (x, some k)) = !f.isDeleted c k := rfl

end Program

/-! ### The value nature of a class in general -/

/-- The deletion facts of a class whose special members are the rules'
own, at every fuel: the copy assignment is deleted exactly when the class
has a reference member, through its class-typed subobjects likewise; the
destructor is never deleted; and with no reference member no special
member is deleted. The resolution for each subobject's corresponding
member selects the implicit member of the same form, by the lemmas above,
so a deletion below is a deletion above. -/
theorem implicit_deleted (p : Program) : ∀ fuel c, p.implicitWithin fuel c = true →
    (p.deletedWithin fuel c .copyAssign = p.referenceMemberWithin fuel c) ∧
    (p.deletedWithin fuel c .dtor = false) ∧
    (p.referenceMemberWithin fuel c = false → ∀ k, p.deletedWithin fuel c k = false) := by
  intro fuel
  induction fuel with
  | zero => intro c h; simp [Program.implicitWithin] at h
  | succ n ih =>
    intro c h
    obtain ⟨-, -, hw, hsub⟩ := implicitWithin_succ p n c h
    -- The facts at fuel `n` about each subobject of class type.
    have hfor : ∀ m ∈ p.classSubobjects c, (p.factsWithin n).implicitFor m :=
      fun m hm k => specialWithin_implicit p n m (hsub m hm) k
    have hisDel : ∀ m ∈ p.classSubobjects c, ∀ k, (p.factsWithin n).isDeleted m k = p.deletedWithin n m k := by
      intro m hm k
      have hk := hfor m hm k
      simp only [Program.factsWithin] at hk
      simp [Program.Facts.isDeleted, Program.factsWithin, hk, Smf.implicit]
    have hdtor : ((p.classSubobjects c).any fun m => (p.factsWithin n).isDeleted m .dtor) = false :=
      List.any_eq_false.mpr fun m hm => by simp [hisDel m hm, (ih m (hsub m hm)).2.1]
    -- For a subobject `t` of class type `M`, what each resolution selects.
    have hsubFacts : ∀ t ∈ p.subobjectsOf c, t.stripConst.isClass = true →
        t.stripConst ∈ p.classSubobjects c ∧ t.stripConst.isConst = false ∧
        p.conversionsOf t.stripConst = [] ∧ (p.factsWithin n).implicitFor t.stripConst := by
      intro t ht hc
      have hm := Program.mem_classSubobjects p c t ht hc
      exact ⟨hm, Program.wellFormed_subobject p c t hw ht,
        implicitWithin_conversions p n _ (hsub _ hm), hfor _ hm⟩
    have hctor0 : ∀ t ∈ p.subobjectsOf c, t.stripConst.isClass = true →
        Program.usable (p.factsWithin n) t.stripConst
          (Program.resolveCtor (p.factsWithin n) p .direct t.stripConst []) =
          !p.deletedWithin n t.stripConst .defaultCtor := by
      intro t ht hc
      obtain ⟨hm, -, hconv, hf⟩ := hsubFacts t ht hc
      rw [resolveCtor_nullary _ p _ hconv hf, Program.usable_selected, hisDel _ hm]
    have hctorL : ∀ t ∈ p.subobjectsOf c, t.stripConst.isClass = true → ∀ cp,
        Program.usable (p.factsWithin n) t.stripConst
          (Program.resolveCtor (p.factsWithin n) p .direct t.stripConst [Program.subobjectArg t cp false]) =
          !p.deletedWithin n t.stripConst .copyCtor := by
      intro t ht hc cp
      obtain ⟨hm, hMc, hconv, hf⟩ := hsubFacts t ht hc
      rcases Program.subobjectArg_copy t cp with ha | ha <;> rw [ha]
      · rw [resolveCtor_lvalue _ p _ hc hMc hconv hf _ (Or.inl rfl), Program.usable_selected, hisDel _ hm]
      · rw [resolveCtor_lvalue _ p _ hc hMc hconv hf _ (Or.inr rfl), Program.usable_selected, hisDel _ hm]
    have hassignL : ∀ t ∈ p.subobjectsOf c, t.stripConst.isClass = true → ∀ cp,
        Program.usable (p.factsWithin n) t.stripConst
          (Program.resolveAssign (p.factsWithin n) p t.stripConst (Program.subobjectArg t cp false)) =
          !p.deletedWithin n t.stripConst .copyAssign := by
      intro t ht hc cp
      obtain ⟨hm, hMc, -, hf⟩ := hsubFacts t ht hc
      rcases Program.subobjectArg_copy t cp with ha | ha <;> rw [ha]
      · rw [resolveAssign_lvalue _ p _ hc hMc hf _ (Or.inl rfl), Program.usable_selected, hisDel _ hm]
      · rw [resolveAssign_lvalue _ p _ hc hMc hf _ (Or.inr rfl), Program.usable_selected, hisDel _ hm]
    -- The copy assignment is deleted exactly by a reference member.
    have hca : p.deletedWithin (n + 1) c .copyAssign = p.referenceMemberWithin (n + 1) c := by
      rw [Program.deletedWithin_copyAssign, Program.referenceMemberWithin,
        Bool.eq_iff_iff]
      simp only [Bool.or_eq_true]
      rw [Program.any_classSubobjects_iff]
      simp only [List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true]
      constructor
      · rintro ((⟨m, hm, hconst, -⟩ | ⟨m, hm, href⟩) | ⟨t, ht, hcls, hc⟩)
        · exact Or.inl ⟨m.ty, Program.mem_subobjectsOf_of_member p c m hm, Or.inr hconst⟩
        · exact Or.inl ⟨m.ty, Program.mem_subobjectsOf_of_member p c m hm, Or.inl href⟩
        · rcases hc with hc | hu
          · exact Or.inl ⟨t, ht, Or.inr hc⟩
          · refine Or.inr ⟨t, ht, hcls, ?_⟩
            rw [hassignL t ht hcls, Bool.not_eq_false', (ih _ (hsub _ (hsubFacts t ht hcls).1)).1] at hu
            exact hu
      · rintro (⟨t, ht, h⟩ | ⟨t, ht, hcls, hr⟩)
        · have ht' := ht
          simp only [Program.subobjectsOf, List.mem_append, List.mem_map] at ht'
          rcases ht' with ⟨m, hm, rfl⟩ | hb
          · rcases h with href | hconst
            · exact Or.inl (Or.inr ⟨m, hm, href⟩)
            · by_cases hcls : m.ty.stripConst.isClass = true
              · exact Or.inr ⟨m.ty, ht, hcls, Or.inl hconst⟩
              · exact Or.inl (Or.inl ⟨m, hm, hconst, Bool.eq_false_iff.mpr hcls⟩)
          · obtain ⟨-, hbc, hbr⟩ := Program.wellFormed_base p c t hw hb
            rcases h with h | h
            · rw [hbr] at h; cases h
            · rw [hbc] at h; cases h
        · refine Or.inr ⟨t, ht, hcls, Or.inr ?_⟩
          rw [hassignL t ht hcls, (ih _ (hsub _ (hsubFacts t ht hcls).1)).1, hr]; rfl
    refine ⟨hca, by rw [Program.deletedWithin_dtor]; exact hdtor, ?_⟩
    -- With no reference member, nothing is deleted.
    intro hR k
    have hR' := hR
    simp only [Program.referenceMemberWithin, Bool.or_eq_false_iff, List.any_eq_false] at hR'
    obtain ⟨hplain, hcsR⟩ := hR'
    have hplain' : ∀ t ∈ p.subobjectsOf c, t.isReference = false ∧ t.isConst = false :=
      fun t ht => by simpa using hplain t ht
    have hnone : ∀ t ∈ p.subobjectsOf c, t.stripConst.isClass = true →
        ∀ k, p.deletedWithin n t.stripConst k = false := by
      intro t ht hc k
      have hm := (hsubFacts t ht hc).1
      exact (ih _ (hsub _ hm)).2.2 (by simpa using hcsR _ hm) k
    have hnoRef : ∀ m ∈ p.membersOf c, m.ty.isReference = false ∧ m.ty.isConst = false :=
      fun m hm => hplain' m.ty (Program.mem_subobjectsOf_of_member p c m hm)
    cases k with
    | defaultCtor =>
      rw [Program.deletedWithin_defaultCtor]
      simp only [Bool.or_eq_false_iff]
      refine ⟨⟨⟨⟨List.any_eq_false.mpr fun m hm => by simp [(hnoRef m hm).1],
        List.any_eq_false.mpr fun m hm => by simp [(hnoRef m hm).2]⟩,
        List.any_eq_false.mpr fun m hm => ?_⟩, List.any_eq_false.mpr fun b hb => ?_⟩, hdtor⟩
      · by_cases hc : m.ty.stripConst.isClass = true
        · simp [hctor0 _ (Program.mem_subobjectsOf_of_member p c m hm) hc,
            hnone _ (Program.mem_subobjectsOf_of_member p c m hm) hc]
        · simp [hc]
      · obtain ⟨hbcl, hbc, -⟩ := Program.wellFormed_base p c b hw hb
        have hbs := stripConst_of_not_const b hbc
        have hc' : b.stripConst.isClass = true := by rw [hbs]; exact hbcl
        have h1 := hctor0 b (Program.mem_subobjectsOf_of_base p c b hb) hc'
        have h2 := hnone b (Program.mem_subobjectsOf_of_base p c b hb) hc' .defaultCtor
        rw [hbs] at h1 h2
        simp [h1, h2]
    | copyCtor =>
      rw [Program.deletedWithin_copyCtor]
      simp only [Bool.or_eq_false_iff]
      refine ⟨⟨List.any_eq_false.mpr fun t ht => ?_, hdtor⟩, ?_⟩
      · by_cases hc : t.stripConst.isClass = true
        · simp [hctorL t ht hc, hnone t ht hc]
        · simp [hc]
      · exact List.any_eq_false.mpr fun m hm => by
          have := (hnoRef m hm).1
          simp only [Ty.isReference, Bool.or_eq_false_iff] at this
          simp [this.2]
    | moveCtor =>
      rw [Program.deletedWithin_moveCtor]
      simp only [Bool.or_eq_false_iff]
      refine ⟨List.any_eq_false.mpr fun t ht => ?_, hdtor⟩
      by_cases hc : t.stripConst.isClass = true
      · obtain ⟨hm, hMc, hconv, hf⟩ := hsubFacts t ht hc
        have hd : (p.factsWithin n).deleted t.stripConst .moveCtor = false := hnone t ht hc .moveCtor
        have ha : ∀ cp, Program.subobjectArg t cp true = { ty := t.stripConst, lvalue := false } :=
          fun cp => Program.subobjectArg_move t cp (hplain' t ht).2
        simp [ha, resolveCtor_rvalue_move _ p _ hc hMc hconv hf hd, Program.usable_selected,
          hisDel _ hm, hnone t ht hc]
      · simp [hc]
    | copyAssign => rw [hca]; exact hR
    | moveAssign =>
      rw [Program.deletedWithin_moveAssign]
      simp only [Bool.or_eq_false_iff]
      refine ⟨⟨List.any_eq_false.mpr fun m hm => by simp [(hnoRef m hm).2],
        List.any_eq_false.mpr fun m hm => by simp [(hnoRef m hm).1]⟩,
        List.any_eq_false.mpr fun t ht => ?_⟩
      by_cases hc : t.stripConst.isClass = true
      · obtain ⟨hm, hMc, -, hf⟩ := hsubFacts t ht hc
        have hd : (p.factsWithin n).deleted t.stripConst .moveAssign = false := hnone t ht hc .moveAssign
        have ha : ∀ cp, Program.subobjectArg t cp true = { ty := t.stripConst, lvalue := false } :=
          fun cp => Program.subobjectArg_move t cp (hplain' t ht).2
        simp [ha, (hplain' t ht).2, resolveAssign_rvalue_move _ p _ hc hMc hf hd, Program.usable_selected,
          hisDel _ hm, hnone t ht hc]
      · simp [hc]
    | dtor => rw [Program.deletedWithin_dtor]; exact hdtor

/-- A class whose special members are the rules' own has value nature
exactly when it has no reference member: no subobject of reference or
`const` type, through class-typed members and bases to any depth. The
author's data and codata, for every class the rules alone construct;
`value_nature_flat` is the case without class-typed subobjects. -/
theorem value_nature_iff (p : Program) (c : Ty) (hc : p.implicitClass c = true) :
    p.valueNature c = !p.referenceMember c := by
  have hsp := specialWithin_implicit p p.length c hc
  obtain ⟨hca, -, hnone⟩ := implicit_deleted p p.length c hc
  unfold Program.valueNature Program.referenceMember
  simp only [Program.special, Program.deleted, hsp, Smf.implicit, List.all_cons, List.all_nil,
    beq_self_eq_true, Bool.true_and, Bool.and_true]
  cases hR : p.referenceMemberWithin p.length c
  · simp [hnone hR]
  · simp [hca, hR]

/-- The copy assignment of a class whose special members are the rules'
own is deleted exactly when the class has a reference member: the one
special member that every reference or `const` member, at any depth,
deletes. -/
theorem copy_assignment_deleted_iff (p : Program) (c : Ty) (hc : p.implicitClass c = true) :
    p.deleted c .copyAssign = p.referenceMember c :=
  (implicit_deleted p p.length c hc).1

/-- A flat class with well-formed declarations is a class whose special
members are the rules' own. -/
theorem flat_implicit (p : Program) (c : Ty) (hc : p.flatClass c = true)
    (hw : p.subobjectsWellFormed c = true) (hl : 0 < p.length) : p.implicitClass c = true := by
  simp only [Program.flatClass, Bool.and_eq_true, List.isEmpty_iff] at hc
  obtain ⟨⟨⟨hs, hconv⟩, hb⟩, hm⟩ := hc
  have hcs : p.classSubobjects c = [] := by
    simp only [Program.classSubobjects, Program.subobjectsOf, hb, List.append_nil, List.filterMap_map]
    simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hm
    rw [List.filterMap_eq_nil_iff]
    intro m hmem
    simp [Function.comp, (hm m hmem).2]
  unfold Program.implicitClass
  obtain ⟨n, hn⟩ : ∃ n, p.length = n + 1 := ⟨p.length - 1, by omega⟩
  rw [hn]
  simp [Program.implicitWithin, hs, hconv, hw, hcs]

/-- A subobject whose class has a deleted special member deletes the
enclosing class's defaulted member of the same kind at the next fuel,
when the subobject's class is one whose special members are the rules'
own, since the resolution for the subobject then selects that member.
The default constructor is deleted through a base or through a member
without a default member initializer, which the rule exempts. A
defaulted move member that is defined as deleted is not a candidate
([class.copy.ctor]/10, [class.copy.assign]/7), so for the move kinds
the resolution falls back to the copy member, and the deletion
propagates when that member is deleted too. -/
theorem deletion_propagates (p : Program) (fuel : Nat) (c t : Ty) (k : SmfKind)
    (ht : t ∈ p.subobjectsOf c) (hcls : t.stripConst.isClass = true)
    (hw : p.subobjectsWellFormed c = true)
    (hM : p.implicitWithin fuel t.stripConst = true)
    (hdel : p.deletedWithin fuel t.stripConst k = true)
    (hinit : k = .defaultCtor → t ∈ p.directBases c ∨ ∃ d ∈ p.membersOf c, d.ty = t ∧ d.init = false)
    (hmove : k = .moveCtor → p.deletedWithin fuel t.stripConst .copyCtor = true)
    (hmoveA : k = .moveAssign → p.deletedWithin fuel t.stripConst .copyAssign = true) :
    p.deletedWithin (fuel + 1) c k = true := by
  have hMc := Program.wellFormed_subobject p c t hw ht
  have hconv := implicitWithin_conversions p fuel _ hM
  have hf : (p.factsWithin fuel).implicitFor t.stripConst := specialWithin_implicit p fuel _ hM
  have hm := Program.mem_classSubobjects p c t ht hcls
  have hisDel : ∀ k, (p.factsWithin fuel).isDeleted t.stripConst k = p.deletedWithin fuel t.stripConst k := by
    intro k
    have hk := hf k
    simp only [Program.factsWithin] at hk
    simp [Program.Facts.isDeleted, Program.factsWithin, hk, Smf.implicit]
  cases k with
  | defaultCtor =>
    rw [Program.deletedWithin_defaultCtor]
    simp only [Bool.or_eq_true]
    rcases hinit rfl with hb | ⟨d, hd, rfl, hdi⟩
    · refine Or.inl (Or.inr (List.any_eq_true.mpr ⟨t, hb, ?_⟩))
      have hbs := stripConst_of_not_const t (Program.wellFormed_base p c t hw hb).2.1
      have h1 := resolveCtor_nullary (p.factsWithin fuel) p t.stripConst hconv hf
      have h2 := hisDel .defaultCtor
      rw [hbs] at h1 h2
      simp [h1, Program.usable_selected, h2, hbs ▸ hdel]
    · refine Or.inl (Or.inl (Or.inr (List.any_eq_true.mpr ⟨d, hd, ?_⟩)))
      simp [hcls, hdi, resolveCtor_nullary (p.factsWithin fuel) p _ hconv hf, Program.usable_selected,
        hisDel, hdel]
  | copyCtor =>
    rw [Program.deletedWithin_copyCtor]
    simp only [Bool.or_eq_true]
    refine Or.inl (Or.inl (List.any_eq_true.mpr ⟨t, ht, ?_⟩))
    rcases Program.subobjectArg_copy t (((p.specialWithin (fuel + 1) c .copyCtor).map (·.constParam)).getD true)
      with ha | ha <;> rw [ha]
    · simp [hcls, resolveCtor_lvalue _ p _ hcls hMc hconv hf _ (Or.inl rfl), Program.usable_selected, hisDel, hdel]
    · simp [hcls, resolveCtor_lvalue _ p _ hcls hMc hconv hf _ (Or.inr rfl), Program.usable_selected, hisDel, hdel]
  | moveCtor =>
    rw [Program.deletedWithin_moveCtor]
    simp only [Bool.or_eq_true]
    refine Or.inl (List.any_eq_true.mpr ⟨t, ht, ?_⟩)
    have hcopy := hmove rfl
    cases htc : t.isConst
    · rw [Program.subobjectArg_move t _ htc]
      have hd : (p.factsWithin fuel).deleted t.stripConst .moveCtor = true := hdel
      simp [hcls, resolveCtor_rvalue_copy _ p _ hcls hMc hconv hf _ (Or.inl ⟨rfl, hd⟩),
        Program.usable_selected, hisDel, hcopy]
    · rw [Program.subobjectArg_move_const t _ htc]
      simp [hcls, resolveCtor_rvalue_copy _ p _ hcls hMc hconv hf _ (Or.inr rfl),
        Program.usable_selected, hisDel, hcopy]
  | copyAssign =>
    rw [Program.deletedWithin_copyAssign]
    simp only [Bool.or_eq_true]
    refine Or.inr (List.any_eq_true.mpr ⟨t, ht, ?_⟩)
    rcases Program.subobjectArg_copy t (((p.specialWithin (fuel + 1) c .copyAssign).map (·.constParam)).getD true)
      with ha | ha <;> rw [ha]
    · simp [hcls, resolveAssign_lvalue _ p _ hcls hMc hf _ (Or.inl rfl), Program.usable_selected, hisDel, hdel]
    · simp [hcls, resolveAssign_lvalue _ p _ hcls hMc hf _ (Or.inr rfl), Program.usable_selected, hisDel, hdel]
  | moveAssign =>
    rw [Program.deletedWithin_moveAssign]
    simp only [Bool.or_eq_true]
    refine Or.inr (List.any_eq_true.mpr ⟨t, ht, ?_⟩)
    have hcopy := hmoveA rfl
    cases htc : t.isConst
    · rw [Program.subobjectArg_move t _ htc]
      have hd : (p.factsWithin fuel).deleted t.stripConst .moveAssign = true := hdel
      simp [hcls, resolveAssign_rvalue_copy _ p _ hcls hMc hf _ (Or.inl ⟨rfl, hd⟩),
        Program.usable_selected, hisDel, hcopy]
    · simp [hcls]
  | dtor =>
    rw [Program.deletedWithin_dtor]
    exact List.any_eq_true.mpr ⟨t.stripConst, hm, by rw [hisDel]; exact hdel⟩

end Overload
