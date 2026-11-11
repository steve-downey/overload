-- Overload/Object/Launder.lean                                       -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Object.Machine

/-!
# When `std::launder` and `std::start_lifetime_as` are necessary

The theorems here are the Standard's own examples run through the
machine, and the statements that say why the two library functions
exist. Each is a computation: a trace, the outcome the model gives it,
and the outcome of the same trace with the call removed.

* `std::launder` is needed when a new object is created in the storage
  of an old one that it does not transparently replace: a const complete
  object ([ptr.launder]/6) or a base class subobject ([ptr.launder]/5).
  Pointers to the old object keep pointing to it, dead, and using them
  is undefined; `std::launder` gives a pointer to the new one. When the
  old object is transparently replaceable, the pointers follow and
  `std::launder` is the identity ([basic.life]/10).
* `std::start_lifetime_as` is needed when storage holds the bytes of an
  object of type `T` and no operation created a `T` there: storage that
  belonged to an object of another type, or a byte buffer filled one
  byte at a time after an object of another type was created in it.
  Where an operation that implicitly creates objects produced the bytes,
  `malloc` or `memcpy`, the call is not needed ([intro.object]/13, /16).

The names are the Standard's: `X`, `C`, `Pair`, `B`, `D`.
-/

namespace Overload.Object

open Machine

namespace Launder

private def int : Ty := .named "int"
private def uchar : Ty := .named "unsigned char"
private def short : Ty := .named "short"
private def cX : Ty := .named "X"
private def cC : Ty := .named "C"
private def cPair : Ty := .named "Pair"
private def cB : Ty := .named "B"
private def cD : Ty := .named "D"

/-- `struct X { int n; }; struct C { int i; }; struct Pair { short a; short b; };
struct B { int b; }; struct D : B { int d; };` -/
def model : Model :=
  { program :=
      [ .class "X", .member cX { name := "n", ty := int }
      , .class "C", .member cC { name := "i", ty := int }
      , .class "Pair", .member cPair { name := "a", ty := short }, .member cPair { name := "b", ty := short }
      , .class "B", .member cB { name := "b", ty := int }
      , .class "D" [cB], .member cD { name := "d", ty := int } ] }

/-- The value a trace read into `v`. -/
def valueOf (t : Trace) (v : String) : Option Value := (run model t).state?.bind (·.val? v)

/-! ## [ptr.launder]/6

```c++
struct X { int n; };
const X *p = new const X{3};
const int a = p->n;
new (const_cast<X*>(p)) const X{5};   // p does not point to new object because its type is const
const int b = p->n;                   // undefined behavior
const int c = std::launder(p)->n;     // OK
```
-/

/-- The example up to the placement `new`. -/
def ptrLaunder6 : Trace :=
  [ .newObject "p" (.const cX) (.braces [3])
  , .member "pn" "p" 0, .read "a" "pn"
  , .cast "q" cX "p"
  , .placementNew "p2" (.const cX) "q" (.braces [5]) ]

/-- `a` is 3. -/
@[std example "ptr.launder#6"]
theorem ptr_launder_6_a : valueOf ptrLaunder6 "a" = some (.int 3) := by decide

/-- `b = p->n` is undefined behaviour: `p` points to the old object,
whose lifetime ended, and a const complete object is not transparently
replaceable. -/
@[std example "ptr.launder#6" "basic.life#9"]
theorem ptr_launder_6_b :
    run model (ptrLaunder6 ++ [.member "pn2" "p" 0, .read "b" "pn2"]) = .undefined .outsideLifetime := by
  decide

/-- `c = std::launder(p)->n` is 5. -/
@[std example "ptr.launder#6" "ptr.launder#3"]
theorem ptr_launder_6_c :
    valueOf (ptrLaunder6 ++ [.launder "l" "p", .member "ln" "l" 0, .read "c" "ln"]) "c" = some (.int 5) := by
  decide

/-! ## [basic.life]/10

```c++
struct C { int i; void f(); const C& operator=(const C&); };
const C& C::operator=(const C& other) {
  if (this != &other) {
    this->~C();                 // lifetime of *this ends
    new (this) C(other);        // new object of type C created
    f();                        // well-defined
  }
  return *this;
}
```
A non-const complete object of the same type is transparently
replaceable, so the pointer refers to the new object without
`std::launder`. -/
def basicLife10 : Trace :=
  [ .var "c" cC (.braces [1]), .addr "p" "c"
  , .destroy "p", .placementNew "p2" cC "p" (.braces [2]) ]

/-- The old pointer reads the new object's value. -/
@[std example "basic.life#10"]
theorem basic_life_10_follows : valueOf (basicLife10 ++ [.member "pi" "p" 0, .read "v" "pi"]) "v" = some (.int 2) := by
  decide

/-- The name of the variable refers to the new object too. -/
@[std example "basic.life#10"]
theorem basic_life_10_name :
    valueOf (basicLife10 ++ [.addr "p3" "c", .member "pi" "p3" 0, .read "v" "pi"]) "v" = some (.int 2) := by
  decide

/-- `std::launder` on a pointer that already follows is the identity on
what it points to. -/
@[std note "ptr.launder#5"]
theorem launder_identity_when_replaceable :
    valueOf (basicLife10 ++ [.launder "l" "p", .member "li" "l" 0, .read "v" "li"]) "v" = some (.int 2) := by
  decide

/-- Between the destructor call and the new object, the old pointer
refers to an object outside its lifetime and accessing a member through
it is undefined. -/
@[std example "basic.life#10" "basic.life#7"]
theorem basic_life_10_between :
    run model [.var "c" cC (.braces [1]), .addr "p" "c", .destroy "p", .member "pi" "p" 0] =
      .undefined .outsideLifetime := by
  decide

/-! ## A base class subobject is never transparently replaced

[ptr.launder]/5: "unless its complete object is a const object or it is
a base class subobject". `struct D : B { int d; }; D d; B* pb = &d;
new (pb) B{7};` creates a complete `B` in the base's storage: `d`'s
lifetime ends, `pb` keeps pointing to the dead base subobject, and
`std::launder(pb)` finds the new `B`. -/
def baseReplaced : Trace :=
  [ .var "d" cD (.braces [1, 2]), .addr "pd" "d", .member "pb" "pd" 0
  , .placementNew "nb" cB "pb" (.braces [7]) ]

/-- Through the old base pointer: undefined. -/
@[std note "ptr.launder#5"]
theorem base_not_replaced : run model (baseReplaced ++ [.member "pbb" "pb" 0, .read "v" "pbb"]) =
    .undefined .outsideLifetime := by
  decide

/-- Through `std::launder`: 7. -/
@[std note "ptr.launder#5"]
theorem base_laundered :
    valueOf (baseReplaced ++ [.launder "l" "pb", .member "lb" "l" 0, .read "v" "lb"]) "v" = some (.int 7) := by
  decide

/-- The containing `D` is dead: its storage was reused by an object not
nested within it. -/
@[std note "basic.life#2"]
theorem base_replaced_kills_complete :
    run model (baseReplaced ++ [.member "pdd" "pd" 1]) = .undefined .outsideLifetime := by
  decide

/-! ## `std::start_lifetime_as`

`int x = 0x00020001; auto* q = reinterpret_cast<Pair*>(&x);` Reading a
member through `q` is undefined: no `Pair` object exists, and an `int`
is not type-accessible through a `short` glvalue. After
`std::start_lifetime_as<Pair>(&x)` a `Pair` exists whose object
representation is the `int`'s bytes, and the `int`'s lifetime has
ended. -/
def reinterpretInt : Trace := [.var "x" int (.scalar 0x00020001), .addr "p" "x", .cast "q" cPair "p"]

@[std note "basic.lval#11" "basic.life#7"]
theorem reinterpret_without_lifetime :
    run model (reinterpretInt ++ [.member "qa" "q" 0, .read "v" "qa"]) = .undefined .typeInaccessible := by
  decide

@[std example "obj.lifetime#5"]
theorem start_lifetime_as_reads_bytes :
    valueOf (reinterpretInt ++ [.startLifetimeAs "r" cPair "p", .member "ra" "r" 0, .read "a" "ra",
      .member "rb" "r" 1, .read "b" "rb"]) "a" = some (.int 1) ∧
    valueOf (reinterpretInt ++ [.startLifetimeAs "r" cPair "p", .member "ra" "r" 0, .read "a" "ra",
      .member "rb" "r" 1, .read "b" "rb"]) "b" = some (.int 2) := by
  decide

@[std example "basic.life#2"]
theorem start_lifetime_as_ends_old :
    run model (reinterpretInt ++ [.startLifetimeAs "r" cPair "p", .read "v" "p"]) = .undefined .outsideLifetime := by
  decide

/-- A `Pair` read as an `int` after `start_lifetime_as<int>`: the bytes
are the pair's. -/
@[std example "obj.lifetime#5"]
theorem start_lifetime_as_round_trip :
    valueOf [.var "pr" cPair (.braces [1, 2]), .addr "p" "pr", .startLifetimeAs "r" int "p", .read "v" "r"] "v" =
      some (.int 0x00020001) := by
  decide

/-! ## A byte buffer filled byte by byte

`unsigned char buf[8];` provides storage, and its creation implicitly
creates the objects that give the program defined behaviour: the `Pair`
read first. Bytes then stored one at a time create nothing, so a later
read as an `int` finds no `int` and is undefined; `start_lifetime_as<int>`
makes it defined; and `memcpy`, which implicitly creates objects in its
destination, makes the call unnecessary. -/
def buffer : Trace := [.var "buf" uchar .default false 8, .addr "b" "buf", .storeBytes "b" [1, 0, 2, 0]]

def bufferAsPair : Trace := buffer ++ [.cast "q" cPair "b", .member "qa" "q" 0, .read "v" "qa"]

@[std example "intro.object#16" "intro.object#3"]
theorem buffer_first_use : valueOf bufferAsPair "v" = some (.int 1) := by decide

@[std note "intro.object#13"]
theorem buffer_reuse_undefined :
    run model (bufferAsPair ++ [.storeBytes "b" [9, 0, 0, 0], .cast "r" int "b", .read "w" "r"]) =
      .undefined .typeInaccessible := by
  decide

@[std example "obj.lifetime#5"]
theorem buffer_reuse_start_lifetime_as :
    valueOf (bufferAsPair ++ [.storeBytes "b" [9, 0, 0, 0], .startLifetimeAs "r" int "b", .read "w" "r"]) "w" =
      some (.int 9) := by
  decide

@[std example "cstring.syn#3"]
theorem buffer_reuse_memcpy :
    valueOf (bufferAsPair ++ [.var "y" int (.scalar 9), .addr "py" "y", .memcpy "b" "py" 4,
      .cast "r" int "b", .read "w" "r"]) "w" = some (.int 9) := by
  decide

/-! ## `malloc` ([intro.object]/15) -/

@[std example "intro.object#15"]
theorem malloc_implicitly_creates :
    valueOf [.malloc "m" 4, .cast "p" cX "m", .member "pn" "p" 0, .write "pn" 1, .read "v" "pn"] "v" =
      some (.int 1) := by
  decide

end Launder

end Overload.Object
