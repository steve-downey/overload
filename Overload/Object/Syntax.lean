-- Overload/Object/Syntax.lean                                        -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Object.Storage

/-!
# The operations of the abstract machine

The syntax of a trace: how a definition initializes its object, the
operations, and a function as a trace with pointer parameters. The
meaning is in `Overload/Object/Machine.lean`; the syntax is separate so
that the model (`Overload/Object/Model.lean`) can carry the functions a
trace calls.
-/

namespace Overload.Object

/-- How a definition or a `new` initializes the object. -/
inductive Init where
  /-- No initializer: default-initialization ([dcl.init.general]/11),
  which for a scalar performs no initialization and for a class calls
  its default constructor. -/
  | default
  /-- Value-initialization, `T()` or `T{}` for a class that is not an
  aggregate: zero-initialization unless the default constructor is
  user-provided, then default-initialization ([dcl.init.general]/8). -/
  | value
  /-- A scalar initialized from a constant, `T x = v;`. -/
  | scalar (v : Int)
  /-- Aggregate initialization from a braced list of constants, one per
  scalar leaf in order; the leaves not listed are value-initialized
  ([dcl.init.aggr]/4, /6). -/
  | braces (vs : List Int)
  deriving Repr, DecidableEq, Inhabited

attribute [std rule "dcl.init.general#11" "dcl.init.general#6"] Init.default
attribute [std rule "dcl.init.general#8"] Init.value
attribute [std rule "dcl.init.general#15"] Init.scalar
attribute [std rule "dcl.init.aggr#4" "dcl.init.aggr#6"] Init.braces

/-- One operation of the abstract machine. Pointers and read values are
named; `x` is the name the operation binds. -/
inductive Op where
  /-- `T x init;` at block scope: automatic storage duration, erroneous
  bytes, or indeterminate ones with `[[indeterminate]]`; with `count`
  above one, `unsigned char x[count]`, the byte array that provides
  storage. -/
  | var (x : String) (ty : Ty) (init : Init := .default) (indeterminate : Bool := false)
      (count : Nat := 1)
  /-- `T x init;` at namespace scope: static storage duration, zero-
  initialized before its initialization. -/
  | staticVar (x : String) (ty : Ty) (init : Init := .default)
  /-- `void* x = malloc(size);`: dynamic storage, indeterminate bytes, an
  operation that implicitly creates objects. -/
  | malloc (x : String) (size : Nat)
  /-- `free(p);`: the storage is released. -/
  | free (p : String)
  /-- `T* x = new T init;`. -/
  | newObject (x : String) (ty : Ty) (init : Init := .default)
  /-- `delete p;`: the destructor, then the storage is released. -/
  | delete (p : String)
  /-- `T* x = ::new (at) T init;`, or `std::construct_at` for
  value-initialization: an object created in the storage `at` points
  into. -/
  | placementNew (x : String) (ty : Ty) (q : String) (init : Init := .default)
  /-- `p->~T();` or `std::destroy_at(p)`. -/
  | destroy (p : String)
  /-- `T* x = std::start_lifetime_as<T>(p);`. -/
  | startLifetimeAs (x : String) (ty : Ty) (p : String)
  /-- `std::start_lifetime(*p);`. -/
  | startLifetime (p : String)
  /-- `T* x = std::launder(p);`. -/
  | launder (x : String) (p : String)
  /-- `T* x = reinterpret_cast<T*>(p);`, or `static_cast<T*>` from a
  `void*`. -/
  | cast (x : String) (ty : Ty) (p : String)
  /-- `T* x = &var;`. -/
  | addr (x : String) (var : String)
  /-- `E* x = &p->e;` for the `i`th element, bases then members. -/
  | member (x : String) (p : String) (i : Nat)
  /-- `auto v = *p;`: the lvalue-to-rvalue conversion of a scalar. -/
  | read (v : String) (p : String)
  /-- `*p = n;`. -/
  | write (p : String) (n : Int)
  /-- `std::memcpy(dst, src, n);`. -/
  | memcpy (dst src : String) (n : Nat)
  /-- Bytes written into storage one at a time through `unsigned char`
  lvalues, by a loop or a `read` system call: not an operation that
  implicitly creates objects. -/
  | storeBytes (p : String) (bs : List Nat)
  /-- `T* x = now_init(p);`, P4222R3's unverified assertion that the
  memory `p` refers to has been initialized: the identity on the
  pointer, with no effect on any object (`Overload/Object/P4222.lean`). -/
  | nowInit (x : String) (p : String)
  /-- `x = f(args);`: a call of the function `f` of the model with
  pointer arguments, binding `x` to the pointer it returns, if any. The
  body runs in its own block with its own names, on the caller's
  objects. -/
  | call (x : Option String) (f : String) (args : List String)
  /-- `{`: a block begins. -/
  | beginBlock
  /-- `}`: the block's automatic objects are destroyed in reverse order
  of creation and their storage released. -/
  | endBlock
  deriving Repr, DecidableEq, Inhabited

attribute [std rule "basic.stc.auto#1" "dcl.attr.indet#1" "basic.indet#1"] Op.var
attribute [std rule "basic.stc.static#1" "basic.start.static#2"] Op.staticVar
attribute [std rule "intro.object#16" "basic.indet#1"] Op.malloc Op.newObject
attribute [std rule "basic.stc.dynamic.deallocation#5"] Op.free
attribute [std rule "expr.delete#5" "basic.stc.dynamic.deallocation#5"] Op.delete
attribute [std rule "basic.life#2" "intro.object#2"] Op.placementNew
attribute [std rule "class.dtor#16" "class.dtor#18" "expr.call#4"] Op.destroy
attribute [std rule "obj.lifetime#3" "obj.lifetime#4" "obj.lifetime#5"] Op.startLifetimeAs
attribute [std rule "obj.lifetime#1" "obj.lifetime#2"] Op.startLifetime
attribute [std rule "ptr.launder#1" "ptr.launder#2" "ptr.launder#3"] Op.launder
attribute [std rule "expr.static.cast#12" "expr.reinterpret.cast#7"] Op.cast
attribute [std rule "basic.life#7"] Op.member
attribute [std rule "conv.lval#1"] Op.read
attribute [std rule "basic.lval#10"] Op.write
attribute [std rule "cstring.syn#3"] Op.memcpy
attribute [std rule "basic.stc.auto#1" "class.dtor#14"] Op.endBlock

/-- A program of the object model: a trace. -/
abbrev Trace := List Op

/-- A function of the object model: its pointer parameters, each a
pointer variable of the body with its pointee type, its body as a trace,
and the pointer variable it returns, if any. A call runs the callee on
the caller's objects with its own names (`Op.call`). -/
structure FunDef where
  name : String
  params : List (String × Ty) := []
  body : Trace := []
  ret : Option String := none
  deriving Repr, DecidableEq, Inhabited


end Overload.Object
