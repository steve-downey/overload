-- Overload/Object/Model.lean                                         -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Object.Storage
import Overload.Aggregate
import Overload.Traits

/-!
# The types the object model lays out

The object model takes its classes from the Standard side's `Program`:
their elements, bases then members ([dcl.init.aggr]/2), whether a
special member is trivial, user-provided or deleted, whether the class is
an aggregate, an implicit-lifetime class, trivially copyable or
standard-layout. What the object model adds is layout, which the type
system never needed: the size of a type and the offset of each element.
Layout is sequential with no padding, the fragment's one implementation
(`decisions.md#object-representation`).

Unions are the object model's own. The Standard side's classes are all
non-union, and a union is declared here by name with its members; its
special members are the implicit trivial ones, so a union of the
fragment is an aggregate and an implicit-lifetime class
(`decisions.md#object-fragment`).

A user-provided default constructor has a body the model does not have.
The model keeps what the body does to the object's bytes: the elements
it initializes and the values it gives them, as `ctorInits`; every other
element is left as default-initialization leaves it, which for a scalar
is no initialization at all ([dcl.init.general]/6).
-/

namespace Overload.Object

/-- The program, with the object model's additions. -/
structure Model where
  program : Program
  /-- Unions, by name, with their members. -/
  unions : List (String × List Member) := []
  /-- What a user-provided default constructor initializes: for a class,
  the elements by index with the value each is given. -/
  ctorInits : List (Ty × List (Nat × Int)) := []
  deriving Inhabited

namespace Model

/-- The class name of a class type, without cv-qualification. -/
def className? (t : Ty) : Option String :=
  match t.stripConst with
  | .named n => if n.isEmpty || fundamentalName n then none else some n
  | _ => none

/-- Is the type a union declared to the object model? -/
@[std rule "class.union.general#1"]
def isUnion (m : Model) (t : Ty) : Bool :=
  match className? t with
  | some n => m.unions.any (·.1 == n)
  | none => false

/-- The data members of a type: a union's declared members, a class's
from the program. -/
def membersOf (m : Model) (t : Ty) : List Member :=
  match className? t with
  | some n =>
    match m.unions.find? (·.1 == n) with
    | some (_, ms) => ms
    | none => m.program.membersOf t.stripConst
  | none => []

/-- The elements of a class type: its direct bases in declaration order
then its direct non-static data members in declaration order; a union's
are its members. -/
@[std rule "dcl.init.aggr#2"]
def elements (m : Model) (t : Ty) : List Ty :=
  if m.isUnion t then (m.membersOf t).map (·.ty)
  else m.program.elements t.stripConst

/-- How many of the elements are bases: the leading ones. -/
def baseCount (m : Model) (t : Ty) : Nat :=
  if m.isUnion t then 0 else (m.program.directBases t.stripConst).length

/-- A scalar type of the fragment: an integral type. Pointers are
scalar types too ([basic.types.general]/7), but the fragment stores no
pointer in an object (`decisions.md#object-fragment`). -/
@[std rule "basic.types.general#7"]
def isScalar (t : Ty) : Bool := t.isIntegral

/-- A class type: a class of the program or a union of the model. -/
def isClass (m : Model) (t : Ty) : Bool := t.stripConst.isClass && (className? t).isSome && !m.isUnion t

/-- The size of a type in bytes, within `fuel` levels of nesting: an
integer's from its width; a class's the sum of its elements', at least
one since an object has nonzero size ([intro.object]/8); a union's the
largest of its members' ([class.union.general]/3). -/
@[std rule "intro.object#8" "class.union.general#3"]
def sizeOfWithin (m : Model) : Nat → Ty → Nat
  | 0, _ => 1
  | fuel + 1, t =>
    match t.stripConst with
    | .named n =>
      if isInteger n then integerSize n
      else if m.isUnion t then max 1 (((m.elements t).map (m.sizeOfWithin fuel)).foldl max 0)
      else max 1 ((m.elements t).map (m.sizeOfWithin fuel)).sum
    | _ => 1

/-- Nesting is bounded by the program's length: a class's elements are
declared after it. -/
def depth (m : Model) : Nat := m.program.length + m.unions.length + 2

/-- The size of a type in bytes. -/
def sizeOf (m : Model) (t : Ty) : Nat := m.sizeOfWithin m.depth t

/-- The elements of a type with their offsets: sequential for a class,
all zero for a union, since each member is allocated as if it were the
sole member ([class.union.general]/3). -/
@[std rule "class.union.general#3"]
def layout (m : Model) (t : Ty) : List (Ty × Nat) :=
  if m.isUnion t then (m.elements t).map (·, 0)
  else
    let rec go : List Ty → Nat → List (Ty × Nat)
      | [], _ => []
      | e :: es, off => (e, off) :: go es (off + m.sizeOf e)
    go (m.elements t) 0

/-- The scalar leaves of a type with their offsets, in declaration order,
within `fuel`: the constituent values of an object of the type
([intro.object]/12), a union contributing its first member alone, the one
that an aggregate initialization initializes. -/
@[std rule "intro.object#12"]
def leavesWithin (m : Model) : Nat → Ty → Nat → List (Ty × Nat)
  | 0, _, _ => []
  | fuel + 1, t, off =>
    if isScalar t then [(t, off)]
    else if m.isUnion t then
      match m.layout t with
      | (e, o) :: _ => m.leavesWithin fuel e (off + o)
      | [] => []
    else (m.layout t).flatMap fun (e, o) => m.leavesWithin fuel e (off + o)

/-- The scalar leaves of a type, from offset zero. -/
def leaves (m : Model) (t : Ty) : List (Ty × Nat) := m.leavesWithin m.depth t 0

/-- An implicit-lifetime type: a scalar type, an implicit-lifetime class,
or an array type ([basic.types.general]/7); a union of the model is an
aggregate whose destructor is not user-provided, so it is one
([class.prop]/8). -/
@[std rule "basic.types.general#7"]
def implicitLifetime (m : Model) (t : Ty) : Bool :=
  isScalar t || m.isUnion t || (m.isClass t && m.program.implicitLifetimeClass t.stripConst)

/-- An aggregate: a union of the model, or an aggregate class of the
program. -/
@[std rule "dcl.init.aggr#1"]
def aggregate (m : Model) (t : Ty) : Bool :=
  m.isUnion t || (m.isClass t && m.program.aggregate t.stripConst)

/-- A trivially copyable type: a scalar, a union of the model, or a
trivially copyable class ([basic.types.general]/7). -/
@[std rule "basic.types.general#7"]
def triviallyCopyable (m : Model) (t : Ty) : Bool :=
  isScalar t || m.isUnion t || (m.isClass t && m.program.triviallyCopyableClass t.stripConst)

/-- Has the class a user-provided default constructor? -/
def userProvidedDefaultCtor (m : Model) (t : Ty) : Bool :=
  m.isClass t && (m.program.userDeclared t.stripConst .defaultCtor).any (·.body == .userProvided)

/-- Does default-initialization of the class select a trivial default
constructor that is not deleted: the condition under which an assignment
to a union member of that type begins its lifetime
([class.union.general]/5), and under which its default-initialization is
vacuous ([basic.life]/2)? A scalar counts as having one, since no
initialization is performed for it. -/
@[std rule "class.union.general#5" "basic.life#2"]
def trivialDefaultCtor (m : Model) (t : Ty) : Bool :=
  isScalar t || m.isUnion t ||
    (m.isClass t && m.program.trivial t.stripConst .defaultCtor && !m.program.isDeleted t.stripConst .defaultCtor)

/-- Is the class's default constructor usable: present and not deleted? A
union of the model has the implicit one. -/
def hasDefaultCtor (m : Model) (t : Ty) : Bool :=
  isScalar t || m.isUnion t || (m.isClass t && m.program.eligible t.stripConst .defaultCtor)

/-- Has the class a non-trivial destructor, one that is invoked
implicitly at block exit ([basic.life]/11)? -/
@[std rule "class.dtor#8"]
def nontrivialDtor (m : Model) (t : Ty) : Bool :=
  m.isClass t && !m.program.trivial t.stripConst .dtor

/-- Is the class standard-layout? A union of the model is. -/
def standardLayout (m : Model) (t : Ty) : Bool :=
  m.isUnion t || (m.isClass t && m.program.standardLayoutClass t.stripConst)

/-- What a user-provided default constructor of the class initializes. -/
def ctorInitsOf (m : Model) (t : Ty) : List (Nat × Int) :=
  match m.ctorInits.find? (·.1 == t.stripConst) with
  | some (_, is) => is
  | none => []

end Model

end Overload.Object
