-- Overload/Object/Machine.lean                                       -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Object.State

/-!
# The abstract machine

A program of the object model is a list of operations: definitions,
allocations, placement `new`, destructor calls, reads and writes through
pointers, `std::launder`, `std::start_lifetime_as`, `std::start_lifetime`,
`memcpy`, P4222R3's `now_init`, calls of the model's functions, and
block entry and exit. `step` runs one on a state and
produces a `Behavior`, `run` the list. There are no expressions beyond a
pointer variable and a constant: the fragment is the traces the lifetime
rules are about, not the language that produces them
(`decisions.md#object-fragment`).

Three rules give the machine its shape.

* **Creation reuses storage** ([basic.life]/2). Creating an object at an
  address ends the lifetime of every object whose storage it overlaps and
  that it is not nested within, with two exceptions: an array of
  `unsigned char` that provides storage for it ([intro.object]/3), and a
  subobject it corresponds to ([intro.object]/2), which makes the new
  object a subobject of the same containing object. If a replaced object
  was transparently replaceable by the new one, pointers to it follow
  ([basic.life]/9, /10); if not, they keep pointing to the dead object,
  and `std::launder` is how a pointer to the new one is obtained.
* **An access needs a live, type-accessible object** ([basic.life]/7,
  /8, [basic.lval]/11). Indirection through a pointer forms a glvalue;
  reading or writing through it is undefined if it refers to no object,
  to one outside its lifetime, or to one of a type the glvalue's type
  does not reach. Reading an indeterminate value is undefined and an
  erroneous one erroneous ([basic.indet]/2).
* **Some storage implicitly creates objects** ([intro.object]/13, /16).
  Storage from an allocation function, an array of `unsigned char` when
  its lifetime begins, and the destination of `memcpy` implicitly create
  the objects of implicit-lifetime type that give the program defined
  behaviour. The model creates them when they are first needed, at the
  first glvalue of their type formed at their address, provided no object
  created since the operation overlaps them
  (`decisions.md#implicit-creation`).
-/

namespace Overload.Object

namespace Machine

open State

/-- The integer type name of a scalar. -/
def scalarName (t : Ty) : String :=
  match t.stripConst with
  | .named n => n
  | _ => ""

/-- Is the type `unsigned char` or `std::byte`, the types whose
indeterminate and erroneous values propagate rather than misbehave
([basic.indet]/2)? -/
@[std rule "basic.indet#2"]
def isByteType (t : Ty) : Bool :=
  t.stripConst == .named "unsigned char" || t.stripConst == .named "std::byte"

/-- Create an object of type `ty` at an address, with its subobjects,
within `fuel` levels of nesting. A class's subobjects are created with
it: alive when the object is, except that a union's members are not
within their lifetime until one is initialized ([class.union.general]/2)
and, when `implicitOnly` is set, a subobject that is not of
implicit-lifetime type is created but its lifetime not started
([intro.object]/13). Returns the new state and the object's identity. -/
@[std rule "intro.object#2" "class.union.general#2" "intro.object#13"]
def createWithin (m : Model) : Nat → State → Ty → Nat → RegionId → Nat → Option ObjId → Bool → Bool → Life →
    Bool → State × ObjId
  | 0, s, ty, count, r, off, parent, isBase, um, life, _ =>
    let id := s.objects.length
    let ob : Obj := { ty, count, region := r, offset := off, size := count * m.sizeOf ty, life, parent,
                      isBase, unionMember := um }
    ({ s with objects := s.objects ++ [ob] }, id)
  | fuel + 1, s, ty, count, r, off, parent, isBase, um, life, implicitOnly =>
    let id := s.objects.length
    let ob : Obj := { ty, count, region := r, offset := off, size := count * m.sizeOf ty, life, parent,
                      isBase, unionMember := um }
    let s := { s with objects := s.objects ++ [ob] }
    if count != 1 then (s, id)
    else
      let bases := m.baseCount ty
      let union := m.isUnion ty
      let s := (m.layout ty).zipIdx.foldl (fun s ((e, o), i) =>
        let childLife :=
          if union then .notStarted
          else if implicitOnly && !m.implicitLifetime e then .notStarted
          else if life == .constructing then .notStarted
          else life
        (createWithin m fuel s e 1 r (off + o) (some id) (decide (i < bases)) union childLife implicitOnly).1) s
      (s, id)

/-- Create an object with its subobjects. -/
def create (m : Model) (s : State) (ty : Ty) (count : Nat) (r : RegionId) (off : Nat)
    (parent : Option ObjId) (life : Life) (implicitOnly : Bool := false) : State × ObjId :=
  createWithin m m.depth s ty count r off parent false false life implicitOnly

/-- The bytes of a region from an offset. -/
def bytesAt (s : State) (r : RegionId) (off n : Nat) : List Byte :=
  match s.region? r with
  | some rg => (rg.bytes.drop off).take n
  | none => []

/-- Replace the bytes of a region from an offset. -/
def writeBytes (s : State) (r : RegionId) (off : Nat) (bs : List Byte) : State :=
  s.updateRegion r fun rg =>
    { rg with bytes := rg.bytes.zipIdx.map fun (b, i) =>
        if off ≤ i && i < off + bs.length then bs[i - off]?.getD b else b }

/-- Does the range lie within allocated storage of the region? -/
def allocated (s : State) (r : RegionId) (off n : Nat) : Bool :=
  match s.region? r with
  | some rg => !rg.released && off + n ≤ rg.bytes.length
  | none => false

/-- The children of an object, in declaration order. -/
def childrenOf (s : State) (o : ObjId) : List ObjId :=
  (s.objects.zipIdx.filter fun (ob, _) => ob.parent == some o).map (·.2)

/-- Begin the lifetime of an object and of its subobjects, every one;
for a union member, end the lifetime of the union's other members first,
since at most one is active ([class.union.general]/2). -/
@[std rule "class.union.general#2"]
def activate (s : State) (o : ObjId) : State :=
  let s :=
    match s.obj? o with
    | some { unionMember := true, parent := some u, .. } =>
      (childrenOf s u).foldl (fun (s : State) c => if c == o then s else s.endLifetime c) s
    | _ => s
  let members := o :: s.subobjectsOf o
  { s with objects := s.objects.zipIdx.map fun (x : Obj × Nat) =>
      if members.contains x.2 && x.1.life != Life.ended then { x.1 with life := .alive } else x.1 }

/-- Begin the lifetime of one object alone, as `std::start_lifetime`
does: no subobject has its lifetime started ([obj.lifetime]/2). For a
union member, the other members' lifetimes end. -/
@[std rule "obj.lifetime#2"]
def activateAlone (s : State) (o : ObjId) : State :=
  let s :=
    match s.obj? o with
    | some { unionMember := true, parent := some u, .. } =>
      (childrenOf s u).foldl (fun (s : State) c => if c == o then s else s.endLifetime c) s
    | _ => s
  s.updateObj o fun ob => { ob with life := .alive }

/-- Storage reuse ([basic.life]/2): an object of type `ty` is about to be
created at an address. Creating it within the storage of a const
complete object of static or automatic storage duration is undefined
([basic.life]/12). If the storage exactly overlays a subobject `e` of an
object within its lifetime, `e` not potentially-overlapping and of the
same type, the new object is a subobject of `e`'s containing object
([intro.object]/2); otherwise it is a complete object. The lifetime of
every other overlapped object the new object is not nested within ends,
except an array that provides storage for it. Returns the state and the
parent, if any. -/
@[std rule "basic.life#2" "basic.life#12" "intro.object#2" "intro.object#3"]
def reuse (m : Model) (s : State) (ty : Ty) (r : RegionId) (off : Nat) : Behavior (State × Option ObjId) :=
  let n := m.sizeOf ty
  let overlapping := s.objectsOverlapping r off n
  let constComplete := overlapping.any fun o =>
    (s.obj? o).any fun ob =>
      ob.isConst && ob.parent.isNone && (s.region? r).any (·.duration != .dynamic)
  if constComplete then .undefined .constStorageReuse
  else
    let corresponding := overlapping.find? fun e =>
      (s.obj? e).any fun eb =>
        eb.offset == off && eb.size == n && !eb.isBase && eb.ty.stripConst == ty.stripConst &&
          eb.count == 1 && eb.parent.isSome && eb.parent.any s.alive
    let parent := corresponding.bind fun e => (s.obj? e).bind (·.parent)
    let keep (o : ObjId) : Bool :=
      -- The containing object and its ancestors survive when the new
      -- object replaces one of their subobjects; a byte array providing
      -- storage survives.
      (match parent with
       | some p => o == p || s.nestedWithin p o
       | none => false) ||
      ((s.obj? o).any fun ob => ob.isByteArray && ob.life == .alive && contains ob.offset ob.size off n)
    let s := overlapping.foldl (fun s o => if keep o then s else s.endLifetime o) s
    .defined (s, parent)

/-- Can an object of type `ty` be taken as implicitly created at an
address ([intro.object]/13, /16): the range lies in one an operation
implicitly created objects in, the type is an implicit-lifetime type, no
object created since that operation overlaps the range, and every object
from before it that overlaps the range is either a byte array providing
storage for it or one the operation could have ended the lifetime of by
reusing its storage: not const, and not used since the operation
(`decisions.md#implicit-creation`)? -/
@[std rule "intro.object#13" "intro.object#16"]
def implicitlyCreatable (m : Model) (s : State) (ty : Ty) (r : RegionId) (off : Nat) : Bool :=
  let n := m.sizeOf ty
  m.implicitLifetime ty && allocated s r off n &&
    match s.region? r with
    | some rg =>
      rg.implicit.any fun ir =>
        contains ir.offset ir.size off n &&
          (s.objectsOverlapping r off n).all fun o =>
            if o ≥ ir.epochObjects then false
            else (s.obj? o).any fun ob =>
              (ob.isByteArray && ob.life == .alive && contains ob.offset ob.size off n) ||
              (ob.lastUse < ir.epochClock && !ob.isConst)
    | none => false

/-- The object of type `ty` within its lifetime at an address, found or
implicitly created: what a pointer to a suitable created object points
to ([intro.object]/14). Implicit creation reuses the storage like any
creation ([basic.life]/2). -/
@[std rule "intro.object#14"]
def pointAt (m : Model) (s : State) (ty : Ty) (r : RegionId) (off : Nat) : State × Option ObjId :=
  match s.liveObjectAt ty r off with
  | some o => (s, some o)
  | none =>
    if implicitlyCreatable m s ty r off then
      match reuse m s ty r off with
      | .defined (s, parent) =>
        let (s, o) := create m s ty 1 r off parent .alive true
        (s, some o)
      | _ => (s, none)
    else (s, none)

/-- Indirection: the object a pointer's glvalue denotes ([expr.unary.op]/1).
A pointer to an object denotes that object, or the one that transparently
replaced it ([basic.life]/10), within its lifetime or not; a pointer into
storage denotes the object of the pointer's type found or implicitly
created there, and refers to no object otherwise ([basic.life]/7); the
null and invalid pointer values point to nothing ([basic.compound]/6). -/
@[std rule "expr.unary.op#1" "basic.life#7" "basic.compound#6"]
def deref (m : Model) (s : State) (p : Ptr) : Behavior (State × ObjId) :=
  match p.loc with
  | .object o => let o := s.resolve o; .defined (s.touch o, o)
  | .storage r off =>
    if !allocated s r off 0 then .undefined .invalidPointer
    else
      match pointAt m s p.ty r off with
      | (s, some o) => .defined (s.touch o, o)
      | (_, none) => .undefined .noObject
  | .null => .undefined .nullPointer
  | .invalid => .undefined .invalidPointer

/-- The union member whose lifetime an assignment through the glvalue
denoting `o` begins ([class.union.general]/5): the outermost object on
the parent chain from `o` that is not within its lifetime, when that
object is a member of a union within its lifetime and every type on the
chain has a trivial default constructor that is not deleted. -/
@[std rule "class.union.general#5"]
def unionActivation (m : Model) (s : State) (o : ObjId) : Option ObjId :=
  let rec go : Nat → ObjId → Option ObjId
    | 0, _ => none
    | fuel + 1, o =>
      match s.obj? o with
      | some ob =>
        if ob.life == .alive || !m.trivialDefaultCtor ob.ty then none
        else if ob.unionMember then
          match ob.parent with
          | some u => if s.alive u then some o else none
          | none => none
        else
          match ob.parent with
          | some p => go fuel p
          | none => none
      | none => none
  go s.objects.length o

/-- The lvalue-to-rvalue conversion through a pointer ([conv.lval]). The
glvalue must denote an object within its lifetime ([basic.life]/8) that
is type-accessible through the glvalue's type ([basic.lval]/11); the
value is decoded from the object representation, and an indeterminate
value is undefined behaviour, an erroneous one erroneous behaviour,
unless the type is `unsigned char` or `std::byte` ([basic.indet]/2). -/
@[std rule "basic.life#8" "basic.lval#11" "basic.indet#2" "conv.lval#3"]
def readThrough (m : Model) (s : State) (p : Ptr) : Behavior (State × Value) := do
  let (s, o) ← deref m s p
  match s.obj? o with
  | none => .undefined .noObject
  | some ob =>
    if ob.life != .alive then .undefined (if ob.unionMember then .inactiveMember else .outsideLifetime)
    else if !typeAccessible p.ty ob.ty then .undefined .typeInaccessible
    else if !Model.isScalar p.ty then .illFormed .notScalar
    else
      let n := scalarName p.ty
      match decode n (bytesAt s ob.region ob.offset (integerSize n)) with
      | none => .undefined .invalidRepresentation
      | some .indeterminate =>
        if isByteType p.ty then .defined (s, .indeterminate) else .undefined .indeterminateValue
      | some .erroneous =>
        if isByteType p.ty then .defined (s, .erroneous)
        else .erroneous ({ s with errors := s.errors ++ [.erroneousValue] }, .erroneous) .erroneousValue
      | some v => .defined (s, v)

/-- Assignment through a pointer ([expr.assign]). Modifying through a
const glvalue is ill-formed ([basic.lval]/10); the glvalue must denote
an object within its lifetime, except that an assignment to a union
member of scalar or trivially default-constructible class type begins its
lifetime ([class.union.general]/5); the object must be type-accessible
([basic.lval]/11) and not const ([dcl.type.cv]/4). -/
@[std rule "basic.lval#10" "basic.life#8" "class.union.general#5" "basic.lval#11" "dcl.type.cv#4"]
def writeThrough (m : Model) (s : State) (p : Ptr) (v : Int) : Behavior State := do
  if p.ty.isConst then .illFormed .constGlvalue
  else
    let (s, o) ← deref m s p
    match s.obj? o with
    | none => .undefined .noObject
    | some ob =>
      let s ←
        if ob.life == .alive then pure s
        else
          match unionActivation m s o with
          | some u => pure (activate s u)
          | none => .undefined (if ob.unionMember then .inactiveMember else .outsideLifetime)
      if !typeAccessible p.ty ob.ty then .undefined .typeInaccessible
      else if ob.isConst || (s.obj? (s.completeObject o)).any Obj.isConst then .undefined .modifiesConst
      else if !Model.isScalar p.ty then .illFormed .notScalar
      else
        let n := scalarName p.ty
        .defined (writeBytes s ob.region ob.offset (encode v (integerSize n)))

/-- Link every ended object the new object transparently replaces to it
([basic.life]/10). -/
@[std rule "basic.life#10"]
def linkReplacements (s : State) (new : ObjId) : State :=
  (s.overlappingWith new).foldl (fun s o =>
    if (s.obj? o).any (·.life == .ended) && (s.obj? o).any (·.replacedBy.isNone) &&
        s.transparentlyReplaceable o new then
      s.updateObj o fun ob => { ob with replacedBy := some new }
    else s) s

/-- Zero-initialize an object's storage: its scalar leaves' bytes are
zero, padding bits zero, and for a union its first member's
([dcl.init.general]/5). -/
@[std rule "dcl.init.general#5"]
def zeroInit (m : Model) (s : State) (ty : Ty) (r : RegionId) (off : Nat) : State :=
  writeBytes s r off (List.replicate (m.sizeOf ty) Byte.zero)

/-- Default-initialization of an object just created ([dcl.init.general]/6):
a class's default constructor is called, which for a user-provided one
does what `ctorInits` says and for a trivial one nothing, so that the
initialization is vacuous ([basic.life]/2); a default member initializer
gives its member zero; a scalar is not initialized. A class whose default
constructor is deleted or absent cannot be default-initialized. -/
@[std rule "dcl.init.general#6" "basic.life#2"]
def defaultInit (m : Model) (s : State) (o : ObjId) (ty : Ty) (r : RegionId) (off : Nat) : Behavior State :=
  if Model.isScalar ty || m.isUnion ty then .defined s
  else if !m.hasDefaultCtor ty then .illFormed .noDefaultConstructor
  else
    let lay := m.layout ty
    let bases := m.baseCount ty
    -- Default member initializers, then the constructor's own writes.
    let s := (lay.zipIdx.foldl (fun s ((e, eo), i) =>
      if i ≥ bases && ((m.membersOf ty)[i - bases]?.any (·.init)) then zeroInit m s e r (off + eo) else s) s)
    let s := (m.ctorInitsOf ty).foldl (fun s (i, v) =>
      match lay[i]? with
      | some (e, eo) => if Model.isScalar e then writeBytes s r (off + eo) (encode v (integerSize (scalarName e))) else s
      | none => s) s
    let _ := o
    .defined s

/-- Apply an initializer to an object just created at an address. -/
@[std rule "dcl.init.general#8" "dcl.init.general#15" "dcl.init.aggr#4" "dcl.init.aggr#6"]
def applyInit (m : Model) (s : State) (o : ObjId) (ty : Ty) (r : RegionId) (off : Nat) :
    Init → Behavior State
  | .default => defaultInit m s o ty r off
  | .value =>
    let s := if m.userProvidedDefaultCtor ty then s else zeroInit m s ty r off
    let s := if m.isUnion ty then (match childrenOf s o with | c :: _ => activate s c | [] => s) else s
    defaultInit m s o ty r off
  | .scalar v =>
    if Model.isScalar ty then .defined (writeBytes s r off (encode v (integerSize (scalarName ty))))
    else .illFormed .notScalar
  | .braces vs =>
    if Model.isScalar ty then
      match vs with
      | [v] => .defined (writeBytes s r off (encode v (integerSize (scalarName ty))))
      | [] => .defined (zeroInit m s ty r off)
      | _ => .illFormed .notAggregate
    else if !m.aggregate ty then .illFormed .notAggregate
    else
      let s := if m.isUnion ty then (match childrenOf s o with | c :: _ => activate s c | [] => s) else s
      let leaves := m.leaves ty
      if vs.length > leaves.length then .illFormed .notAggregate
      else
        .defined (leaves.zipIdx.foldl (fun s ((e, eo), i) =>
          let v := vs[i]?.getD 0
          writeBytes s r (off + eo) (encode v (integerSize (scalarName e)))) s)

/-- Create an object of type `ty` with an initializer in storage already
obtained, reusing the storage: the general step behind a definition, a
`new` and a placement `new`. -/
def createObject (m : Model) (s : State) (ty : Ty) (r : RegionId) (off : Nat) (init : Init)
    (count : Nat := 1) : Behavior (State × ObjId) := do
  if !allocated s r off (count * m.sizeOf ty) then .undefined .lifetimePrecondition
  else
    let (s, parent) ← reuse m s ty r off
    -- A class with a constructor body is created under construction, its
    -- elements not yet started; `construct` runs the constructor.
    let underConstruction := count == 1 && (m.ctorOf? ty).isSome && (init == .default || init == .value)
    let (s, o) := create m s ty count r off parent (if underConstruction then .constructing else .alive)
    let s := linkReplacements s o
    if underConstruction then .defined (s, o)
    else if count != 1 then
      -- A byte array: its lifetime beginning implicitly creates objects
      -- within it ([intro.object]/16), and value-initialization zeroes it.
      let s := s.updateRegion r fun rg =>
        { rg with implicit := rg.implicit ++ [{ offset := off, size := count * m.sizeOf ty, epochObjects := o + 1, epochClock := s.clock }] }
      let s := if init == .default then s else writeBytes s r off (List.replicate (count * m.sizeOf ty) Byte.zero)
      .defined (s, o)
    else
      let s ← applyInit m s o ty r off init
      .defined (s, o)

/-- A new region of storage. -/
def obtain (s : State) (d : Duration) (bytes : List Byte) (implicit : Bool) : State × RegionId :=
  let r := s.regions.length
  let rg : Region :=
    { duration := d, bytes
      implicit := if implicit then [{ offset := 0, size := bytes.length, epochObjects := s.objects.length, epochClock := s.clock }] else [] }
  ({ s with regions := s.regions ++ [rg] }, r)

/-- Release a region: its duration ends, the lifetime of every object in
it ends ([basic.life]/2), and every pointer into it becomes invalid
([basic.compound]/3, /6). -/
@[std rule "basic.stc.dynamic.deallocation#5" "basic.life#2" "basic.compound#6"]
def release (s : State) (r : RegionId) : State :=
  let s := s.updateRegion r fun rg => { rg with released := true }
  let s := { s with objects := s.objects.map fun (ob : Obj) =>
    if ob.region == r && ob.life == Life.alive then { ob with life := .ended } else ob }
  let invalidate (xp : String × Ptr) : String × Ptr :=
    match s.locAddress xp.2.loc with
    | some (r', _) => if r' == r then (xp.1, { xp.2 with loc := .invalid }) else xp
    | none => xp
  { s with ptrs := s.ptrs.map invalidate }

/-- The region and offset of a pointer's address, or the undefined
behaviour of using a pointer that represents none. -/
def addressOf (s : State) (p : Ptr) (why : Why) : Behavior (RegionId × Nat) :=
  match s.locAddress p.loc with
  | some a => .defined a
  | none => .undefined why

/-- Look a pointer variable up. -/
def ptr (s : State) (x : String) : Behavior Ptr :=
  match s.ptr? x with
  | some p => .defined p
  | none => .illFormed (.unbound x)

/-- Record an automatic object in the innermost block. -/
def inBlock (s : State) (o : ObjId) : State :=
  match s.blocks with
  | b :: bs => { s with blocks := (b ++ [o]) :: bs }
  | [] => s

/-- One step of the machine. -/
def step (m : Model) (s : State) : Op → Behavior State
  | .var x ty init indet count =>
    if s.blocks.isEmpty then .illFormed .noBlock
    else
      let bytes := List.replicate (count * m.sizeOf ty) (if indet then Byte.indeterminate else Byte.erroneous)
      let (s, r) := obtain s .automatic bytes false
      createObject m s ty r 0 init count >>= fun (s, o) =>
        .defined (inBlock (s.setName x o) o)
  | .staticVar x ty init =>
    let (s, r) := obtain s .static (List.replicate (m.sizeOf ty) Byte.zero) false
    createObject m s ty r 0 init >>= fun (s, o) => .defined (s.setName x o)
  | .malloc x size =>
    let (s, r) := obtain s .dynamic (List.replicate size Byte.indeterminate) true
    .defined (s.setPtr x { ty := .named "void", loc := .storage r 0 })
  | .free x => do
    let p ← ptr s x
    match p.loc with
    | .null => .defined s
    | .storage r 0 => if allocated s r 0 0 then .defined (release s r) else .undefined .invalidPointer
    | .object o =>
      match s.obj? (s.resolve o) with
      | some ob =>
        if ob.offset == 0 && ob.parent.isNone && (s.region? ob.region).any (·.duration == .dynamic) &&
            allocated s ob.region 0 0 then
          .defined (release s ob.region)
        else .undefined .notDeletable
      | none => .undefined .notDeletable
    | _ => .undefined .invalidPointer
  | .newObject x ty init =>
    let (s, r) := obtain s .dynamic (List.replicate (m.sizeOf ty) Byte.indeterminate) true
    createObject m s ty r 0 init >>= fun (s, o) => .defined (s.setPtr x { ty, loc := .object o })
  | .delete x => do
    let p ← ptr s x
    match p.loc with
    | .null => .defined s
    | .object o =>
      let o := s.resolve o
      match s.obj? o with
      | some ob =>
        if !(ob.offset == 0 && ob.parent.isNone && (s.region? ob.region).any (·.duration == .dynamic)) then
          .undefined .notDeletable
        else if ob.life != .alive then .undefined .destructorOutsideLifetime
        else .defined (release (s.endLifetime o) ob.region)
      | none => .undefined .notDeletable
    | _ => .undefined .invalidPointer
  | .placementNew x ty  q init => do
    let p ← ptr s q
    let (r, off) ← addressOf s p .invalidPointer
    let (s, o) ← createObject m s ty r off init
    .defined (s.setPtr x { ty, loc := .object o })
  | .destroy q => do
    let p ← ptr s q
    let (s, o) ← deref m s p
    match s.obj? o with
    | none => .undefined .noObject
    | some ob =>
      if ob.ty.stripConst != p.ty.stripConst then .undefined .wrongDestructor
      else if ob.life != .alive then .undefined .destructorOutsideLifetime
      else .defined (s.endLifetime o)
  | .startLifetimeAs x ty q => do
    if !m.implicitLifetime ty then .illFormed .notImplicitLifetime
    else
      let p ← ptr s q
      let (r, off) ← addressOf s p .lifetimePrecondition
      if !allocated s r off (m.sizeOf ty) then .undefined .lifetimePrecondition
      else
        let (s, parent) ← reuse m s ty r off
        let (s, o) := create m s ty 1 r off parent .alive true
        let s := linkReplacements s o
        .defined (s.setPtr x { ty, loc := .object o })
  | .startLifetime q => do
    let p ← ptr s q
    if !(m.implicitLifetime p.ty && m.aggregate p.ty) then .illFormed .notImplicitLifetime
    else
      match p.loc with
      | .object o =>
        let o := s.resolve o
        match s.obj? o with
        | some ob =>
          if ob.ty.stripConst != p.ty.stripConst then .undefined .noObject
          else if ob.life == .alive then .defined s
          else .defined (activateAlone s o)
        | none => .undefined .noObject
      | _ => .undefined .noObject
  | .launder x q => do
    let p ← ptr s q
    if p.ty.isVoid || p.ty.isFunction then .illFormed .notAnObjectPointer
    else
      let (r, off) ← addressOf s p .launderPrecondition
      match s.liveObjectAt p.ty r off with
      | some o => .defined (s.setPtr x { p with loc := .object o })
      | none => .undefined .launderPrecondition
  | .cast x ty q => do
    let p ← ptr s q
    match p.loc with
    | .object o =>
      let o := s.resolve o
      match s.obj? o with
      | none => .defined (s.setPtr x { ty, loc := .object o })
      | some ob =>
        if ob.ty.stripConst == ty.stripConst && ob.count == 1 then
          .defined (s.setPtr x { ty, loc := .object o })
        else
          let same := (s.objectsOverlapping ob.region ob.offset 1).filter fun b =>
            (s.obj? b).any fun bb =>
              bb.offset == ob.offset && bb.life == .alive && bb.ty.stripConst == ty.stripConst && bb.count == 1
          match same.find? fun b => pointerInterconvertible m s o b with
          | some b => .defined (s.setPtr x { ty, loc := .object b })
          | none =>
            match pointAt m s ty ob.region ob.offset with
            | (s, some b) => .defined (s.setPtr x { ty, loc := .object b })
            | (s, none) => .defined (s.setPtr x { ty, loc := .object o })
    | .storage r off =>
      match pointAt m s ty r off with
      | (s, some b) => .defined (s.setPtr x { ty, loc := .object b })
      | (s, none) => .defined (s.setPtr x { ty, loc := .storage r off })
    | loc => .defined (s.setPtr x { ty, loc })
  | .addr x var =>
    match s.name? var with
    | some o =>
      let o := s.resolve o
      match s.obj? o with
      | some ob => .defined (s.setPtr x { ty := ob.ty, loc := .object o })
      | none => .illFormed (.unbound var)
    | none => .illFormed (.unbound var)
  | .member x q i => do
    let p ← ptr s q
    let (s, o) ← deref m s p
    match s.obj? o with
    | none => .undefined .noObject
    | some ob =>
      if ob.ty.stripConst != p.ty.stripConst then .undefined .typeInaccessible
      else if ob.life != .alive && ob.life != .constructing then .undefined .outsideLifetime
      else
        match (childrenOf s o)[i]? with
        | some c =>
          match s.obj? c with
          | some cb => .defined (s.setPtr x { ty := cb.ty, loc := .object c })
          | none => .illFormed (.unbound x)
        | none => .illFormed (.unbound x)
  | .read v q => do
    let p ← ptr s q
    let (s, value) ← readThrough m s p
    .defined (s.setVal v value)
  | .write q n => do
    let p ← ptr s q
    writeThrough m s p n
  | .memcpy dst src n => do
    let pd ← ptr s dst
    let ps ← ptr s src
    let (rs, offs) ← addressOf s ps .invalidPointer
    let (rd, offd) ← addressOf s pd .invalidPointer
    if !(allocated s rs offs n && allocated s rd offd n) then .undefined .invalidPointer
    else if (match ps.loc with | .object o => !s.alive (s.resolve o) | _ => false) then .undefined .outsideLifetime
    else if (match pd.loc with | .object o => !s.alive (s.resolve o) | _ => false) then .undefined .outsideLifetime
    else if (match pd.loc with
             | .object o => (s.obj? (s.completeObject (s.resolve o))).any Obj.isConst
             | _ => false) then .undefined .modifiesConst
    else
      let s := match ps.loc with | .object o => s.touch (s.resolve o) | _ => s
      let s := match pd.loc with | .object o => s.touch (s.resolve o) | _ => s
      let s := writeBytes s rd offd (bytesAt s rs offs n)
      .defined (s.updateRegion rd fun rg =>
        { rg with implicit := rg.implicit ++ [{ offset := offd, size := n, epochObjects := s.objects.length, epochClock := s.clock + 1 }] })
  | .storeBytes q bs => do
    let p ← ptr s q
    let (r, off) ← addressOf s p .invalidPointer
    if !allocated s r off bs.length then .undefined .invalidPointer
    else if (match p.loc with | .object o => !s.alive (s.resolve o) | _ => false) then .undefined .outsideLifetime
    else
      let s := match p.loc with | .object o => s.touch (s.resolve o) | _ => s
      .defined (writeBytes s r off (bs.map Byte.byte))
  | .nowInit x q => do
    let p ← ptr s q
    .defined (s.setPtr x p)
  | .call _ f _ => .illFormed (.badCall f)
  | .beginBlock => .defined { s with blocks := [] :: s.blocks }
  | .endBlock =>
    match s.blocks with
    | [] => .illFormed .noBlock
    | b :: bs =>
      let s := { s with blocks := bs }
      -- Implicit destruction, in reverse order of creation ([class.dtor]/14).
      let destroyed : Behavior State := b.reverse.foldl (fun acc o =>
        acc >>= fun s =>
          match s.obj? o with
          | some ob =>
            if !m.nontrivialDtor ob.ty then .defined s
            else if ob.life == .alive then .defined (s.endLifetime o)
            else
              match s.liveObjectAt ob.ty ob.region ob.offset with
              | some o' => .defined (s.endLifetime o')
              | none => .undefined .implicitDestructor
          | none => .defined s) (.defined s)
      destroyed >>= fun s =>
        .defined (b.foldl (fun s o =>
          match s.obj? o with
          | some ob => release s ob.region
          | none => s) s)

attribute [std rule "class.dtor#14" "basic.life#11" "basic.stc.auto#1"] step

/-- A call: the callee's parameters are bound to the arguments' pointer
values with the parameters' pointee types, the callee's body runs in a
block of its own with its own names on the caller's objects, its block
ends, and the pointer it returns, if any, is read after that, so that a
pointer to one of its automatic objects comes back invalid. The
caller's names, pointers and values are restored. `exec` runs the body. -/
def call (m : Model) (exec : State → Trace → Behavior State) (s : State) (x : Option String) (f : String)
    (args : List String) : Behavior State :=
  match m.function? f with
  | none => .illFormed (.badCall f)
  | some fd =>
    if fd.params.length != args.length then .illFormed (.badCall f)
    else
      let bound : Behavior (List (String × Ptr)) :=
        (fd.params.zip args).foldl (fun acc ((pn, pty), a) =>
          acc >>= fun l => ptr s a >>= fun p => .defined (l ++ [(pn, { p with ty := pty })])) (.defined [])
      bound >>= fun l =>
        let callee : State := { s with names := [], ptrs := l, vals := [], blocks := [] :: s.blocks }
        exec callee fd.body >>= fun s' =>
          step m s' .endBlock >>= fun s'' =>
            let result := fd.ret.bind s''.ptr?
            let back : State := { s'' with names := s.names, ptrs := s.ptrs, vals := s.vals }
            match x, result with
            | some x, some p => .defined (back.setPtr x p)
            | some _, none => .illFormed (.badCall f)
            | none, _ => .defined back

/-- The object a creation operation just made under construction, if it
is one: a definition, `new` or placement `new` of a class with a
constructor body and a default or value initializer. -/
def ctorTarget (m : Model) (s : State) : Op → Option ObjId
  | .var x ty init _ count =>
    if count == 1 && (m.ctorOf? ty).isSome && (init == .default || init == .value) then s.name? x else none
  | .newObject x ty init | .placementNew x ty _ init =>
    if (m.ctorOf? ty).isSome && (init == .default || init == .value) then
      (s.ptr? x).bind fun p => match p.loc with | .object o => some o | _ => none
    else none
  | _ => none

/-- The two phases of a constructor ([class.base.init]/15): the elements
in declaration order, each from its mem-initializer or by
default-initialization, its lifetime beginning when its initialization
completes ([basic.life]/2); then the body, in a block of its own with
`this` bound to the object under construction; the object's lifetime
begins when the constructor returns ([class.base.init]/11). A
mem-initializer that reads an element whose initialization has not
completed reads an object outside its lifetime ([basic.life]/8). -/
@[std rule "class.base.init#15" "class.base.init#11" "class.base.init#12"]
def construct (m : Model) (exec : State → Trace → Behavior State) (s : State) (o : ObjId) : Behavior State :=
  match s.obj? o with
  | none => .illFormed (.unbound "this")
  | some ob =>
    match m.ctorOf? ob.ty with
    | none => .defined s
    | some cd =>
      let kids := childrenOf s o
      let initialized : Behavior State :=
        (m.layout ob.ty).zipIdx.foldl (fun acc ((e, _), i) =>
          acc >>= fun s =>
            match kids[i]? with
            | none => .defined s
            | some c =>
              match s.obj? c with
              | none => .defined s
              | some cb =>
                match cd.memInits.find? (·.1 == i) with
                | some (_, .value v) => applyInit m s c e cb.region cb.offset v >>= fun s => .defined (activate s c)
                | some (_, .fromMember j) =>
                  match kids[j]? with
                  | none => .illFormed (.unbound "member")
                  | some cj =>
                    readThrough m s { ty := e, loc := .object cj } >>= fun (s, _) =>
                      match s.obj? cj with
                      | some cjb =>
                        let s := writeBytes s cb.region cb.offset (bytesAt s cjb.region cjb.offset (m.sizeOf e))
                        .defined (activate s c)
                      | none => .defined s
                | none => applyInit m s c e cb.region cb.offset .default >>= fun s => .defined (activate s c))
          (.defined s)
      initialized >>= fun s =>
        let callee : State :=
          { s with names := [], ptrs := [("this", { ty := ob.ty, loc := .object o })], vals := [],
                   blocks := [] :: s.blocks }
        exec callee cd.body >>= fun s' =>
          step m s' .endBlock >>= fun s'' =>
            .defined (activateAlone { s'' with names := s.names, ptrs := s.ptrs, vals := s.vals } o)

/-- Run a trace from a state, within `fuel` operations counting the
operations of every called body. -/
def exec (m : Model) : Nat → State → Trace → Behavior State
  | 0, _, _ => .illFormed .fuel
  | _, s, [] => .defined s
  | fuel + 1, s, op :: ops =>
    let s := { s with clock := s.clock + 1 }
    (match op with
     | .call x f args => call m (exec m fuel) s x f args
     | _ =>
       step m s op >>= fun s' =>
         match ctorTarget m s' op with
         | some o => construct m (exec m fuel) s' o
         | none => .defined s') >>= fun s => exec m fuel s ops

/-- The fuel a trace is given: enough for every operation and for every
body a call can run, at the model's size. -/
def fuelFor (m : Model) (t : Trace) : Nat :=
  (t.length + 2) * (2 + (m.functions.map (·.body.length + 2)).sum + (m.ctors.map (·.body.length + 2)).sum)

/-- Run a trace from a state. -/
def runFrom (m : Model) (s : State) (t : Trace) : Behavior State := exec m (fuelFor m t) s t

/-- Run a trace from the initial state, inside one block. -/
def run (m : Model) (t : Trace) : Behavior State := runFrom m {} (.beginBlock :: t)

end Machine

end Overload.Object
