-- Overload/Object/Storage.lean                                       -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Types

/-!
# Storage, bytes and behaviour

The object model's ground: storage durations, the bytes a region of
storage is made of and the three states a byte can be in, the value an
object's representation decodes to, and the outcome type of an
evaluation. The outcome type is the object model's counterpart of
`Subst` and `Resolution`: a theorem about "erroneous versus undefined"
is a theorem about which constructor comes out.

Bytes are the Standard's. A byte is indeterminate, erroneous or a value
([basic.indet]/1), and an object's value is decoded from the bytes of
its object representation ([basic.types.general]/2): indeterminate if
any byte is, otherwise erroneous if any byte is, otherwise the value the
bytes represent. The representation of an integer is little-endian two's
complement, which the Standard leaves to the implementation
(`decisions.md#object-representation`).
-/

namespace Overload.Object

/-- The storage duration of an object, one of four
([basic.stc.general]/1). Thread storage duration is named and never
used: the fragment is one thread. -/
inductive Duration where
  | static | thread | automatic | dynamic
  deriving Repr, DecidableEq, Inhabited

attribute [std rule "basic.stc.general#1"] Duration.static Duration.thread Duration.automatic
  Duration.dynamic

/-- A byte of storage. When storage is obtained its bytes are
indeterminate or erroneous ([basic.indet]/1), and an initialization or
an assignment replaces them with values. -/
inductive Byte where
  /-- An indeterminate value: the bytes of dynamic storage, and of a
  variable marked `[[indeterminate]]`. -/
  | indeterminate
  /-- An erroneous value: the bytes of automatic storage otherwise,
  fixed by the implementation independently of the program. -/
  | erroneous
  /-- A byte with a value, `0 ≤ b < 256`. -/
  | byte (b : Nat)
  deriving Repr, DecidableEq, Inhabited

attribute [std rule "basic.indet#1"] Byte.indeterminate Byte.erroneous
attribute [std rule "basic.types.general#2.sentence-1"] Byte.byte

/-- The value of a scalar object, as decoded from its object
representation ([basic.indet]/1 sentences 5 and 6). -/
inductive Value where
  | indeterminate
  | erroneous
  | int (v : Int)
  deriving Repr, DecidableEq, Inhabited

/-- Why an evaluation was not defined, or was erroneous, or a program
ill-formed: the model's reasons, each named for the rule that produces
it. -/
inductive Why where
  /-- Indirection through a null pointer: no object ([expr.unary.op]/1). -/
  | nullPointer
  /-- A pointer to released storage ([basic.compound]/6). -/
  | invalidPointer
  /-- A glvalue of object type refers to allocated storage in which no
  object of that type exists ([basic.life]/7, /8). -/
  | noObject
  /-- An access to an object outside its lifetime ([basic.life]/8). -/
  | outsideLifetime
  /-- An access through a glvalue of a type the object is not
  type-accessible through ([basic.lval]/11). -/
  | typeInaccessible
  /-- An evaluation produced an indeterminate value ([basic.indet]/2). -/
  | indeterminateValue
  /-- An evaluation produced an erroneous value ([basic.indet]/2). -/
  | erroneousValue
  /-- The bits of the value representation are not valid for the type
  ([conv.lval]/3). -/
  | invalidRepresentation
  /-- Modifying a const object during its lifetime ([dcl.type.cv]/4). -/
  | modifiesConst
  /-- Creating an object within the storage of a const complete object
  of static or automatic storage duration ([basic.life]/12). -/
  | constStorageReuse
  /-- A destructor invoked for an object whose lifetime has ended
  ([class.dtor]/18). -/
  | destructorOutsideLifetime
  /-- Block exit with an implicit destructor call for storage no object
  of the original type occupies ([basic.life]/11). -/
  | implicitDestructor
  /-- `std::launder`'s precondition: no object of a similar type within
  its lifetime at the address ([ptr.launder]/2). -/
  | launderPrecondition
  /-- `std::start_lifetime_as`'s precondition: the range is not
  allocated storage ([obj.lifetime]/4). -/
  | lifetimePrecondition
  /-- `std::start_lifetime_as` of a type that is not an implicit-lifetime
  type, or `std::start_lifetime` of one that is not an implicit-lifetime
  aggregate ([obj.lifetime]/1, /3). -/
  | notImplicitLifetime
  /-- An inactive union member accessed, or a union member whose lifetime
  an assignment cannot begin ([class.union.general]/5). -/
  | inactiveMember
  /-- Modifying an object through a glvalue of const type ([basic.lval]/10). -/
  | constGlvalue
  /-- Brace initialization of a class that is not an aggregate
  ([dcl.init.aggr]/1). -/
  | notAggregate
  /-- Default-initialization selected no usable default constructor
  ([dcl.init.general]/6). -/
  | noDefaultConstructor
  /-- A pointer to the wrong kind of thing for the operation. -/
  | notAnObjectPointer
  /-- A read or a write of a value of class type, which the fragment does
  not have: it copies bytes with `memcpy` instead. -/
  | notScalar
  /-- A destructor invoked through a glvalue whose type is not the
  object's class ([class.dtor]/16). -/
  | wrongDestructor
  /-- A deleted pointer that does not point to a complete dynamic object
  ([expr.delete]/2). -/
  | notDeletable
  /-- A name the program never bound. -/
  | unbound (name : String)
  /-- A block-scope definition with no open block. -/
  | noBlock
  deriving Repr, DecidableEq, Inhabited

/-- The outcome of evaluating an operation of the abstract machine.
Defined behaviour carries the next state; erroneous behaviour is
well-defined, so it carries the next state too, and the reason; undefined
behaviour carries only its reason, since no state follows it; and an
ill-formed program is diagnosed before any execution. -/
inductive Behavior (α : Type) where
  /-- The operation is defined and produced `a`. -/
  | defined (a : α)
  /-- The operation has erroneous behaviour: well-defined, the
  implementation recommended to diagnose it and permitted to terminate
  the program. -/
  | erroneous (a : α) (why : Why)
  /-- The operation has undefined behaviour. -/
  | undefined (why : Why)
  /-- The program is ill-formed: a diagnosable rule is violated. -/
  | illFormed (why : Why)
  deriving Repr, DecidableEq, Inhabited

attribute [std rule "intro.abstract#1"] Behavior.defined
attribute [std rule "intro.abstract#6"] Behavior.erroneous
attribute [std rule "intro.abstract#4"] Behavior.undefined
attribute [std rule "intro.compliance.general#2"] Behavior.illFormed

namespace Behavior

/-- Sequencing: an erroneous step is followed by the next, and the first
reason is kept; undefined and ill-formed stop. -/
def bind : Behavior α → (α → Behavior β) → Behavior β
  | .defined a, f => f a
  | .erroneous a w, f =>
    match f a with
    | .defined b => .erroneous b w
    | .erroneous b _ => .erroneous b w
    | .undefined w' => .undefined w'
    | .illFormed w' => .illFormed w'
  | .undefined w, _ => .undefined w
  | .illFormed w, _ => .illFormed w

instance : Monad Behavior where
  pure := .defined
  bind := bind

/-- The state an outcome carries, when it carries one. -/
def state? : Behavior α → Option α
  | .defined a | .erroneous a _ => some a
  | _ => none

/-- Is the outcome defined behaviour, erroneous or not? -/
def isDefined : Behavior α → Bool
  | .defined _ | .erroneous _ _ => true
  | _ => false

/-- Is the outcome undefined behaviour? -/
def isUndefined : Behavior α → Bool
  | .undefined _ => true
  | _ => false

/-- Is the outcome erroneous behaviour? -/
def isErroneous : Behavior α → Bool
  | .erroneous _ _ => true
  | _ => false

/-- Is the program ill-formed? -/
def isIllFormed : Behavior α → Bool
  | .illFormed _ => true
  | _ => false

end Behavior

/-! ## The object representation of an integer -/

/-- The bytes an integer type occupies: the least `k` with `256^k` values
covering its range. From the widths of `integer-widths`: `bool`, `char`
and `unsigned char` one, `short` two, `int` four, `long` eight. -/
def integerSize (n : String) : Nat :=
  match integerRange n with
  | some (lo, hi) =>
    let values := (hi - lo + 1).toNat
    if values ≤ 256 then 1 else if values ≤ 65536 then 2 else if values ≤ 4294967296 then 4 else 8
  | none => 0

/-- Little-endian two's complement: the `k` bytes of `v` modulo `256^k`
(`decisions.md#object-representation`). -/
@[assumed "object-representation"]
def encode (v : Int) (k : Nat) : List Byte :=
  let m : Int := (256 : Int) ^ k
  let u := (v % m).toNat
  (List.range k).map fun i => .byte ((u / 256 ^ i) % 256)

/-- The value the bytes of an integer object of type `n` represent: an
indeterminate value if any byte is indeterminate, otherwise an erroneous
value if any byte is, otherwise the integer they encode; `none` when the
bits are not a valid value representation for the type, which for the
fragment's integers happens for `bool` alone ([conv.lval]/3). -/
@[std rule "basic.indet#1" "conv.lval#3"]
def decode (n : String) (bs : List Byte) : Option Value :=
  if bs.any (· == .indeterminate) then some .indeterminate
  else if bs.any (· == .erroneous) then some .erroneous
  else
    let u : Nat := (bs.zipIdx.map fun (b, i) => match b with | .byte x => x * 256 ^ i | _ => 0).sum
    let k := bs.length
    let m : Int := (256 : Int) ^ k
    match integerRange n with
    | some (lo, _) =>
      let v : Int := if lo < 0 && (u : Int) ≥ m / 2 then (u : Int) - m else u
      if representable n v == some true then some (.int v) else none
    | none => none

/-- A zero byte. -/
def Byte.zero : Byte := .byte 0

end Overload.Object
