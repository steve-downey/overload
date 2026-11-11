-- OverloadTest/Object.lean                                           -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Object.Machine

/-! Tests of the object model's abstract machine: lifetime, storage
reuse, transparent replacement, `std::launder`, `std::start_lifetime_as`,
unions, indeterminate and erroneous values, block exit. -/

open Overload Overload.Object Overload.Object.Machine

private def int : Ty := .named "int"
private def uchar : Ty := .named "unsigned char"
private def short : Ty := .named "short"
private def cX : Ty := .named "X"
private def cC : Ty := .named "C"
private def cPair : Ty := .named "Pair"
private def cB : Ty := .named "B"
private def cT : Ty := .named "T"
private def cU : Ty := .named "U"

/-- `struct X { int n; }; struct C { int i; }; struct Pair { short a; short b; };
struct B { ~B(); int b; }; struct T { T() {} int x; }; union U { int i; short s; };` -/
private def model : Model :=
  { program :=
      [ .class "X", .member cX { name := "n", ty := int }
      , .class "C", .member cC { name := "i", ty := int }
      , .class "Pair", .member cPair { name := "a", ty := short }, .member cPair { name := "b", ty := short }
      , .class "B", .special cB { kind := .dtor }, .member cB { name := "b", ty := int }
      , .class "T", .special cT { kind := .defaultCtor }, .member cT { name := "x", ty := int } ]
    unions := [("U", [{ name := "i", ty := int }, { name := "s", ty := short }])] }

private def value (b : Behavior State) (v : String) : Option Value := b.state?.bind (·.val? v)

-- Sizes and layout.
#guard model.sizeOf int == 4
#guard model.sizeOf cPair == 4
#guard model.sizeOf cU == 4
#guard model.layout cPair == [(short, 0), (short, 2)]
-- `T` has a trivial copy constructor and a trivial destructor, so it is an implicit-lifetime class.
#guard model.implicitLifetime cPair && model.implicitLifetime cU && model.implicitLifetime cT
#guard !model.implicitLifetime cB
#guard model.nontrivialDtor cB && !model.nontrivialDtor cX

-- `int x; auto v = x;` has erroneous behaviour and an erroneous value.
private def readUninit := run model [.var "x" int, .addr "p" "x", .read "v" "p"]
#guard readUninit.isErroneous
#guard value readUninit "v" == some .erroneous

-- `int x [[indeterminate]]; auto v = x;` is undefined.
#guard (run model [.var "x" int .default true, .addr "p" "x", .read "v" "p"]) == .undefined .indeterminateValue

-- `int x = 5;` reads 5; `int x{};` reads 0.
#guard value (run model [.var "x" int (.scalar 5), .addr "p" "x", .read "v" "p"]) "v" == some (.int 5)
#guard value (run model [.var "x" int .value, .addr "p" "x", .read "v" "p"]) "v" == some (.int 0)

-- `int* p = new int; auto v = *p;` is undefined: dynamic storage is indeterminate.
#guard (run model [.newObject "p" int, .read "v" "p"]) == .undefined .indeterminateValue

-- `static int x; auto v = x;` reads 0.
#guard value (run model [.staticVar "x" int, .addr "p" "x", .read "v" "p"]) "v" == some (.int 0)

-- A negative value round-trips through two's complement.
#guard value (run model [.var "x" int (.scalar (-7)), .addr "p" "x", .read "v" "p"]) "v" == some (.int (-7))

/-! [ptr.launder]/6: a const complete object is not transparently
replaceable, so the old pointer does not refer to the new object and
`std::launder` does. -/
private def launderExample (tail : Trace) : Behavior State :=
  run model
    ([ .newObject "p" (.const cX) (.braces [3])
     , .member "pn" "p" 0, .read "a" "pn"
     , .cast "q" cX "p"
     , .placementNew "p2" (.const cX) "q" (.braces [5]) ] ++ tail)

#guard value (launderExample []) "a" == some (.int 3)
#guard (launderExample [.member "pn2" "p" 0, .read "b" "pn2"]) == .undefined .outsideLifetime
#guard value (launderExample [.launder "l" "p", .member "ln" "l" 0, .read "c" "ln"]) "c" == some (.int 5)

/-! [basic.life]/10: a non-const complete object of the same type is
transparently replaced, so the old pointer refers to the new object. -/
private def replaceExample : Behavior State :=
  run model
    [ .var "c" cC (.braces [1]), .addr "p" "c"
    , .destroy "p", .placementNew "p2" cC "p" (.braces [2])
    , .member "pi" "p" 0, .read "v" "pi" ]
#guard value replaceExample "v" == some (.int 2)

-- Reading through the old pointer after the destructor and before the new object is undefined.
#guard (run model [.var "c" cC (.braces [1]), .addr "p" "c", .destroy "p", .member "pi" "p" 0]) ==
  .undefined .outsideLifetime

-- A second destructor call is undefined ([class.dtor]/18).
#guard (run model [.var "c" cC (.braces [1]), .addr "p" "c", .destroy "p", .destroy "p"]) ==
  .undefined .destructorOutsideLifetime

/-! `std::start_lifetime_as`: reading an `int`'s storage as a `Pair`
is undefined; after `start_lifetime_as<Pair>` it is defined and the
bytes are the `int`'s. -/
private def reinterpret (tail : Trace) : Behavior State :=
  run model ([.var "x" int (.scalar 0x00020001), .addr "p" "x", .cast "q" cPair "p"] ++ tail)
#guard (reinterpret [.member "qa" "q" 0, .read "v" "qa"]) == .undefined .typeInaccessible
#guard value (reinterpret [.startLifetimeAs "r" cPair "p", .member "ra" "r" 0, .read "v" "ra"]) "v" == some (.int 1)
#guard value (reinterpret [.startLifetimeAs "r" cPair "p", .member "rb" "r" 1, .read "v" "rb"]) "v" == some (.int 2)
-- The `int`'s lifetime ended when its storage was reused.
#guard (reinterpret [.startLifetimeAs "r" cPair "p", .read "v" "p"]) == .undefined .outsideLifetime
-- `start_lifetime_as` of a type that is not implicit-lifetime is ill-formed.
#guard (reinterpret [.startLifetimeAs "r" cB "p"]) == .illFormed .notImplicitLifetime

/-! Implicit object creation: `malloc` then member writes through `X*`
([intro.object]/15). -/
#guard value (run model [.malloc "m" 4, .cast "p" cX "m", .member "pn" "p" 0, .write "pn" 7, .read "v" "pn"]) "v" ==
  some (.int 7)

/-! A byte buffer: bytes stored one at a time, then read as a `Pair`,
which the buffer's creation implicitly created; stored again and read as
an `int`, which nothing created, undefined until `start_lifetime_as`. -/
private def buffer (tail : Trace) : Behavior State :=
  run model ([.var "buf" uchar .default false 8, .addr "b" "buf", .storeBytes "b" [1, 0, 2, 0]] ++ tail)
#guard value (buffer [.cast "q" cPair "b", .member "qa" "q" 0, .read "v" "qa"]) "v" == some (.int 1)
#guard (buffer [.cast "q" cPair "b", .member "qa" "q" 0, .read "v" "qa", .storeBytes "b" [9, 0, 0, 0],
                .cast "r" int "b", .read "w" "r"]) == .undefined .typeInaccessible
#guard value (buffer [.cast "q" cPair "b", .member "qa" "q" 0, .read "v" "qa", .storeBytes "b" [9, 0, 0, 0],
                .startLifetimeAs "r" int "b", .read "w" "r"]) "w" == some (.int 9)
-- `memcpy` implicitly creates objects in its destination, so no call is needed after it.
#guard value (buffer [.cast "q" cPair "b", .member "qa" "q" 0, .read "v" "qa",
                .var "y" int (.scalar 9), .addr "py" "y", .memcpy "b" "py" 4,
                .cast "r" int "b", .read "w" "r"]) "w" == some (.int 9)

/-! Unions: assignment to a member begins its lifetime and ends the
other's ([class.union.general]/5); reading the inactive member is
undefined. -/
private def unionExample (tail : Trace) : Behavior State :=
  run model ([.var "u" cU, .addr "pu" "u", .member "pi" "pu" 0, .member "ps" "pu" 1, .write "pi" 5] ++ tail)
#guard value (unionExample [.read "v" "pi"]) "v" == some (.int 5)
#guard (unionExample [.read "v" "ps"]) == .undefined .inactiveMember
#guard value (unionExample [.write "ps" 3, .read "v" "ps"]) "v" == some (.int 3)
#guard (unionExample [.write "ps" 3, .read "v" "pi"]) == .undefined .inactiveMember
-- `U u;` activates no member; `U u{};` activates the first.
#guard (run model [.var "u" cU, .addr "pu" "u", .member "pi" "pu" 0, .read "v" "pi"]) == .undefined .inactiveMember
#guard value (run model [.var "u" cU .value, .addr "pu" "u", .member "pi" "pu" 0, .read "v" "pi"]) "v" == some (.int 0)

/-! Block exit: a destroyed object with a non-trivial destructor whose
storage holds no object of its type is undefined ([basic.life]/11); one
replaced by an object of the same type is fine. -/
#guard (run model [.var "b" cB, .addr "p" "b", .destroy "p", .endBlock]) == .undefined .implicitDestructor
#guard (run model [.var "b" cB, .addr "p" "b", .destroy "p", .placementNew "p2" cB "p", .endBlock]).isDefined
#guard (run model [.var "b" cB, .addr "p" "b", .destroy "p", .placementNew "p2" cX "p", .endBlock]) ==
  .undefined .implicitDestructor
#guard (run model [.var "c" cC, .addr "p" "c", .destroy "p", .endBlock]).isDefined

-- A pointer into released storage is invalid.
#guard (run model [.newObject "p" int (.scalar 1), .delete "p", .read "v" "p"]) == .undefined .invalidPointer
#guard (run model [.beginBlock, .var "x" int (.scalar 1), .addr "p" "x", .endBlock, .read "v" "p"]) ==
  .undefined .invalidPointer

/-! `T() {}` leaves `x` erroneous although `T t{};` has an initializer
([dcl.attr.indet]/3). -/
#guard (run model [.var "t" cT .value, .addr "p" "t", .member "px" "p" 0, .read "v" "px"]).isErroneous

-- `now_init` is the identity on the pointer and changes no object.
#guard value (run model [.var "x" int (.scalar 3), .addr "p" "x", .nowInit "q" "p", .read "v" "q"]) "v" == some (.int 3)

/-! Calls: the callee runs on the caller's objects with its own names, a
returned pointer to a callee's automatic object is invalid, and an
unknown function is ill-formed. -/
private def withFns : Model :=
  { model with functions :=
      [ { name := "set", params := [("p", int)], body := [.write "p" 9] }
      , { name := "local", body := [.var "x" int (.scalar 1), .addr "r" "x"], ret := some "r" }
      , { name := "shadow", params := [("p", int)], body := [.var "x" int (.scalar 5), .write "p" 2] } ] }
#guard value (run withFns [.var "x" int (.scalar 1), .addr "p" "x", .call none "set" ["p"], .read "v" "p"]) "v" ==
  some (.int 9)
#guard (run withFns [.call (some "r") "local" [], .read "v" "r"]) == .undefined .invalidPointer
-- The callee's `x` does not replace the caller's.
#guard value (run withFns [.var "x" int (.scalar 1), .addr "p" "x", .call none "shadow" ["p"], .addr "p2" "x",
  .read "v" "p2"]) "v" == some (.int 2)
#guard (run withFns [.call none "nothing" []]) == .illFormed (.badCall "nothing")
