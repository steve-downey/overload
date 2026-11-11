-- Overload/Object/State.lean                                         -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Object.Model

/-!
# Objects, pointers and the machine state

An object occupies a region of storage and has a type, a storage
duration through its region, and a lifetime ([intro.object]/1). The
state keeps every object ever created, within its lifetime or not, since
a pointer that pointed to an object keeps pointing to it after its
lifetime ends and the rules of [basic.life]/7 to /10 are about exactly
those pointers.

A pointer value is one of the Standard's four ([basic.compound]/3): a
pointer to an object, which the model names by the object's identity; a
pointer that represents an address but points to no object, which is
what an allocation function returns before an object is created there
and what a conversion that found no object leaves; the null pointer
value; and an invalid pointer value, which a pointer into released
storage becomes. A pointer carries its static type, since indirection
through it forms a glvalue of that type.

Transparent replacement ([basic.life]/10) is a link from the replaced
object to its replacement, followed when a pointer, a reference or a
name is used: `resolve`.
-/

namespace Overload.Object

/-- An object's identity: its index in the state's object list. -/
abbrev ObjId := Nat

/-- A region's identity: its index in the state's region list. -/
abbrev RegionId := Nat

/-- A range of storage an operation implicitly created objects in
([intro.object]/13, /16), with the epoch of the operation: how many
objects existed and what the clock read when it ran. An object the
operation could have created is one no object created since overlaps and
no object used since would be ended by (`decisions.md#implicit-creation`). -/
structure ImplicitRange where
  offset : Nat
  size : Nat
  epochObjects : Nat
  epochClock : Nat
  deriving Repr, DecidableEq, Inhabited

/-- A region of storage: its duration, its bytes, whether its duration
has ended, and the ranges within it that an operation implicitly created
objects in. -/
structure Region where
  duration : Duration
  bytes : List Byte
  released : Bool := false
  implicit : List ImplicitRange := []
  deriving Repr, DecidableEq, Inhabited

/-- Where an object stands in its lifetime ([basic.life]/2): created but
its lifetime not begun, as a union member that is not active; within its
lifetime; or its lifetime ended. The periods of construction and
destruction ([class.cdtor]) are out of the fragment. -/
inductive Life where
  | notStarted | alive | ended
  deriving Repr, DecidableEq, Inhabited

attribute [std rule "class.union.general#2"] Life.notStarted
attribute [std rule "basic.life#2"] Life.alive Life.ended

/-- An object: it occupies a region of storage, has a type, and has a
storage duration through its region ([intro.object]/1). -/
@[std rule "intro.object#1"]
structure Obj where
  /-- Its type, with any top-level `const`. -/
  ty : Ty
  /-- The number of elements, for an array object; one otherwise. The
  fragment's arrays are arrays of `unsigned char`, the ones that provide
  storage ([intro.object]/3). -/
  count : Nat := 1
  region : RegionId
  offset : Nat
  size : Nat
  life : Life
  /-- The object this one is a subobject of, if any; a complete object
  has none ([intro.object]/2). -/
  parent : Option ObjId := none
  /-- A base class subobject, which is potentially-overlapping
  ([intro.object]/7). -/
  isBase : Bool := false
  /-- A union elemental subobject ([intro.object]/11). -/
  unionMember : Bool := false
  /-- The object that transparently replaced this one, once its lifetime
  ended ([basic.life]/10). -/
  replacedBy : Option ObjId := none
  /-- The clock when a glvalue last denoted this object or one nested in
  it: what implicit creation must not retroactively undo. -/
  lastUse : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- Is the object an array of `unsigned char` or `std::byte`, the kind
that provides storage? -/
@[std rule "intro.object#3"]
def Obj.isByteArray (o : Obj) : Bool :=
  o.count > 1 && (o.ty.stripConst == .named "unsigned char" || o.ty.stripConst == .named "std::byte")

/-- Is the object const: its type is const-qualified? -/
def Obj.isConst (o : Obj) : Bool := o.ty.isConst

/-- What a pointer value designates ([basic.compound]/3). -/
inductive Loc where
  /-- A pointer to an object. -/
  | object (o : ObjId)
  /-- A pointer that represents an address in a region of storage and
  points to no object. -/
  | storage (r : RegionId) (off : Nat)
  /-- The null pointer value. -/
  | null
  /-- An invalid pointer value. -/
  | invalid
  deriving Repr, DecidableEq, Inhabited

attribute [std rule "basic.compound#3"] Loc.object Loc.storage Loc.null Loc.invalid

/-- A pointer: its pointee type and its value. `ty` is `void` for a
`void*`. -/
structure Ptr where
  ty : Ty
  loc : Loc
  deriving Repr, DecidableEq, Inhabited

/-- The state of the abstract machine. -/
structure State where
  regions : List Region := []
  objects : List Obj := []
  /-- The pointer variables of the program, outside the object model. -/
  ptrs : List (String × Ptr) := []
  /-- The values read, by the name the program gave the read. -/
  vals : List (String × Value) := []
  /-- The variables, by name, and the object each names. -/
  names : List (String × ObjId) := []
  /-- The open blocks, innermost first, each with the complete objects of
  automatic storage duration created in it, in order of creation. -/
  blocks : List (List ObjId) := []
  /-- The erroneous behaviour so far: an execution continues past it. -/
  errors : List Why := []
  /-- The number of operations run so far. -/
  clock : Nat := 0
  deriving Repr, DecidableEq, Inhabited

namespace State

def obj? (s : State) (o : ObjId) : Option Obj := s.objects[o]?

def region? (s : State) (r : RegionId) : Option Region := s.regions[r]?

def ptr? (s : State) (x : String) : Option Ptr := (s.ptrs.find? (·.1 == x)).map (·.2)

def val? (s : State) (x : String) : Option Value := (s.vals.find? (·.1 == x)).map (·.2)

def name? (s : State) (x : String) : Option ObjId := (s.names.find? (·.1 == x)).map (·.2)

def setPtr (s : State) (x : String) (p : Ptr) : State :=
  { s with ptrs := (x, p) :: s.ptrs.filter (·.1 != x) }

def setVal (s : State) (x : String) (v : Value) : State :=
  { s with vals := (x, v) :: s.vals.filter (·.1 != x) }

def setName (s : State) (x : String) (o : ObjId) : State :=
  { s with names := (x, o) :: s.names.filter (·.1 != x) }

def updateObj (s : State) (o : ObjId) (f : Obj → Obj) : State :=
  { s with objects := s.objects.zipIdx.map fun (ob, i) => if i == o then f ob else ob }

def updateRegion (s : State) (r : RegionId) (f : Region → Region) : State :=
  { s with regions := s.regions.zipIdx.map fun (rg, i) => if i == r then f rg else rg }

/-- The object a pointer to `o`, a reference to it or its name refers
to now: `o` itself, or the object that transparently replaced it, and so
on ([basic.life]/10). -/
@[std rule "basic.life#10"]
def resolve (s : State) (o : ObjId) : ObjId :=
  let rec go : Nat → ObjId → ObjId
    | 0, o => o
    | fuel + 1, o =>
      match s.obj? o with
      | some { replacedBy := some o', .. } => go fuel o'
      | _ => o
  go s.objects.length o

/-- Do two byte ranges overlap? -/
def overlaps (o₁ n₁ o₂ n₂ : Nat) : Bool := o₁ < o₂ + n₂ && o₂ < o₁ + n₁

/-- Does the first range contain the second? -/
def contains (o₁ n₁ o₂ n₂ : Nat) : Bool := o₁ ≤ o₂ && o₂ + n₂ ≤ o₁ + n₁

/-- The objects, by identity, whose storage overlaps a range of a
region. -/
def objectsOverlapping (s : State) (r : RegionId) (off n : Nat) : List ObjId :=
  (s.objects.zipIdx.filter fun (o, _) => o.region == r && overlaps o.offset o.size off n).map (·.2)

/-- The objects whose storage overlaps that of an object. -/
def overlappingWith (s : State) (o : ObjId) : List ObjId :=
  match s.obj? o with
  | some ob => (s.objectsOverlapping ob.region ob.offset ob.size).filter (· != o)
  | none => []

/-- Does `b` provide storage for `a`: `b` is an array of `unsigned char`
or `std::byte` within its lifetime, `a` a complete object whose storage
fits entirely within `b`'s ([intro.object]/3)? The third condition, no
nested array satisfying the others, holds in a fragment whose byte arrays
are not nested in one another. -/
@[std rule "intro.object#3"]
def providesStorage (s : State) (b a : ObjId) : Bool :=
  match s.obj? b, s.obj? a with
  | some ob, some oa =>
    ob.isByteArray && ob.life == .alive && oa.parent.isNone && b != a &&
      ob.region == oa.region && contains ob.offset ob.size oa.offset oa.size
  | _, _ => false

/-- Is `a` nested within `b`: a subobject of it, provided storage by it,
or nested within an object nested within `b` ([intro.object]/4)? -/
@[std rule "intro.object#4"]
def nestedWithin (s : State) (a b : ObjId) : Bool :=
  let rec go : Nat → ObjId → Bool
    | 0, _ => false
    | fuel + 1, a =>
      match s.obj? a with
      | some oa =>
        (oa.parent == some b) || s.providesStorage b a ||
          (match oa.parent with
           | some p => go fuel p
           | none =>
             -- The object that provides storage for `a`, if any, is the
             -- next step outward.
             match (s.objectsOverlapping oa.region oa.offset oa.size).find? fun c => s.providesStorage c a with
             | some c => go fuel c
             | none => false)
      | none => false
  go s.objects.length a

/-- The complete object of `o`: `o` if it is a subobject of nothing,
otherwise the complete object of the object that contains it
([intro.object]/5). -/
@[std rule "intro.object#5"]
def completeObject (s : State) (o : ObjId) : ObjId :=
  let rec go : Nat → ObjId → ObjId
    | 0, o => o
    | fuel + 1, o =>
      match s.obj? o with
      | some { parent := some p, .. } => go fuel p
      | _ => o
  go s.objects.length o

/-- Is `o₁` transparently replaceable by `o₂` ([basic.life]/9): both
complete objects, `o₁` not const, the storage of `o₂` exactly overlaying
that of `o₁`, the same type ignoring top-level cv-qualifiers; or
corresponding direct subobjects, the same parent and the same storage
and type with neither potentially-overlapping, whose complete object is
not const? `mutable` members are out of the fragment. -/
@[std rule "basic.life#9"]
def transparentlyReplaceable (s : State) (o₁ o₂ : ObjId) : Bool :=
  match s.obj? o₁, s.obj? o₂ with
  | some a, some b =>
    let sameStorage := a.region == b.region && a.offset == b.offset && a.size == b.size
    let sameType := a.ty.stripConst == b.ty.stripConst
    sameStorage && sameType &&
      ((a.parent.isNone && b.parent.isNone && !a.isConst) ||
       (a.parent.isSome && a.parent == b.parent && !a.isBase && !b.isBase &&
         !(s.obj? (s.completeObject o₁)).any Obj.isConst))
  | _, _ => false

/-- Is the object within its lifetime? -/
def alive (s : State) (o : ObjId) : Bool := (s.obj? o).any (·.life == .alive)

/-- The address an object occupies, or occupied. -/
def address (s : State) (o : ObjId) : Option (RegionId × Nat) :=
  (s.obj? o).map fun ob => (ob.region, ob.offset)

/-- The address a pointer value represents ([basic.compound]/3), if it
represents one: a pointer to an object represents the address of the
first byte it occupies or occupied; a pointer into storage represents
that address; the null and invalid pointer values represent none. -/
@[std rule "basic.compound#3"]
def locAddress (s : State) : Loc → Option (RegionId × Nat)
  | .object o => s.address o
  | .storage r off => some (r, off)
  | .null | .invalid => none

/-- The object of type `t`, ignoring cv-qualification, within its
lifetime whose address is `(r, off)`, if there is one; the one created
last when several, which happens for a union and its first member. -/
def liveObjectAt (s : State) (t : Ty) (r : RegionId) (off : Nat) : Option ObjId :=
  (s.objects.zipIdx.filter fun (o, _) =>
    o.region == r && o.offset == off && o.life == .alive && o.ty.stripConst == t.stripConst &&
      o.count == 1).getLast?.map (·.2)

/-- Is an object of dynamic type `tobj` type-accessible through a glvalue
of type `tref` ([basic.lval]/11): `tref` similar to `tobj`, which for
the fragment's types is equality up to top-level `const`; or the signed
or unsigned type corresponding to it; or `char`, `unsigned char` or
`std::byte`? -/
@[std rule "basic.lval#11"]
def typeAccessible (tref tobj : Ty) : Bool :=
  let a := tref.stripConst
  let b := tobj.stripConst
  a == b ||
    (a == .named "char" || a == .named "unsigned char" || a == .named "std::byte") ||
    (a == .named "signed char" && b == .named "unsigned char") ||
    (a == .named "unsigned char" && b == .named "signed char") ||
    (a == .named "int" && b == .named "unsigned") || (a == .named "unsigned" && b == .named "int")

/-- Are two objects pointer-interconvertible ([basic.compound]/7): the
same object; a union and one of its members; a standard-layout class
object and its first member or a base class subobject; or so by a chain?
The chain is followed outward from the inner object: each step is to a
parent at the same address that is a union, or a standard-layout class
whose first element or base the object is. -/
@[std rule "basic.compound#7"]
def pointerInterconvertible (m : Model) (s : State) (a b : ObjId) : Bool :=
  let rec up : Nat → ObjId → List ObjId
    | 0, o => [o]
    | fuel + 1, o =>
      match s.obj? o with
      | some ob =>
        match ob.parent with
        | some p =>
          match s.obj? p with
          | some pb =>
            if pb.offset == ob.offset &&
                (m.isUnion pb.ty || (m.standardLayout pb.ty && (ob.isBase || ob.offset == pb.offset))) then
              o :: up fuel p
            else [o]
          | none => [o]
        | none => [o]
      | none => [o]
  a == b || (up s.objects.length a).contains b || (up s.objects.length b).contains a

/-- Every object nested within `o`, by the parent chain alone: `o`'s
subobjects, transitively. -/
def subobjectsOf (s : State) (o : ObjId) : List ObjId :=
  (s.objects.zipIdx.filter fun (ob, i) => i != o && ob.parent.isSome && s.nestedWithin i o).map (·.2)

/-- The ancestors of an object: its parent, the parent's parent, and so
on. -/
def ancestors (s : State) (o : ObjId) : List ObjId :=
  let rec go : Nat → ObjId → List ObjId
    | 0, _ => []
    | fuel + 1, o =>
      match s.obj? o with
      | some { parent := some p, .. } => p :: go fuel p
      | _ => []
  go s.objects.length o

/-- Record that a glvalue denoted the object now: it, its ancestors and
its subobjects were used. -/
def touch (s : State) (o : ObjId) : State :=
  let ids := o :: s.ancestors o ++ s.subobjectsOf o
  { s with objects := s.objects.zipIdx.map fun (x : Obj × Nat) =>
      if ids.contains x.2 then { x.1 with lastUse := s.clock } else x.1 }

/-- End the lifetime of an object and of everything nested within it. -/
def endLifetime (s : State) (o : ObjId) : State :=
  let victims := o :: s.subobjectsOf o
  { s with objects := s.objects.zipIdx.map fun (ob, i) =>
      if victims.contains i && ob.life == .alive then { ob with life := .ended } else ob }

end State

end Overload.Object
