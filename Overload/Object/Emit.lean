-- Overload/Object/Emit.lean                                          -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Object.Machine
import Overload.Emit

/-!
# Differential cases for the object model

Constant evaluation is the oracle. A core constant expression may not
contain an operation that would have undefined or erroneous behaviour,
an lvalue-to-rvalue conversion of an object with an indeterminate value,
or a read of a non-active union member ([expr.const.core]/2), so a
`static_assert` on a `constexpr` function that runs a trace is
well-formed exactly when the machine gives the trace defined behaviour.
Erroneous behaviour is defined behaviour at run time and is not a
constant expression, so an erroneous trace is expected ill-formed.

Each case pairs a trace with the C++ that spells it; the expectation is
computed from the trace, and `OverloadTest/Emit.lean` checks that the
emitted expectation is the machine's. What constant evaluation cannot
run stays out: `std::start_lifetime_as`, `reinterpret_cast`, `malloc`
and `memcpy` ([expr.const.core]/2, [intro.object]/16), and placement
`new`, which is C++26. `std::construct_at` and `std::destroy_at` stand
in for the last two.
-/

namespace Overload.Object.Emit

open Overload.Emit Overload.Object.Machine

/-- A differential case of the object model: the case the harness
compiles, and the trace and model that computed its expectation. -/
structure ObjectCase where
  case : Case
  trace : Trace
  model : Model

private def int : Ty := .named "int"
private def short : Ty := .named "short"
private def cX : Ty := .named "X"
private def cC : Ty := .named "C"
private def cE : Ty := .named "E"
private def cPair : Ty := .named "Pair"
private def cT : Ty := .named "T"
private def cU : Ty := .named "U"
private def cB : Ty := .named "B"
private def cD : Ty := .named "D"

/-- The classes of the cases. `E` has a user-provided constexpr
destructor, which is the one that is invoked at block exit. -/
def model : Model :=
  { program :=
      [ .class "X", .member cX { name := "n", ty := int }
      , .class "C", .member cC { name := "i", ty := int }
      , .class "E", .special cE { kind := .dtor }, .member cE { name := "e", ty := int }
      , .class "Pair", .member cPair { name := "a", ty := short }, .member cPair { name := "b", ty := short }
      , .class "T", .special cT { kind := .defaultCtor }, .member cT { name := "x", ty := int }
      , .class "B", .member cB { name := "b", ty := int }
      , .class "D" [cB], .member cD { name := "d", ty := int } ]
    unions := [("U", [{ name := "i", ty := int }, { name := "s", ty := short }])] }

/-- The declarations every case's C++ starts with. -/
def classes : String :=
  "#include <memory>\n#include <new>\n" ++
  "struct X { int n; };\nstruct C { int i; };\n" ++
  "struct E { int e; constexpr ~E() {} };\n" ++
  "struct Pair { short a; short b; };\n" ++
  "struct T { constexpr T() {} int x; };\n" ++
  "union U { int i; short s; };\n" ++
  "struct B { int b; };\nstruct D : B { int d; };\n" ++
  "constexpr void destroy(C* p) { std::destroy_at(p); }\n"

/-- Is the trace defined behaviour, with no erroneous behaviour: the
condition under which its constant evaluation is a constant expression
([expr.const.core]/2)? -/
@[std rule "expr.const.core#2"]
def constant (m : Model) (t : Trace) : Bool := (run m t) matches .defined _

private def cite (s : String) : Overload.Std.Citation :=
  match Overload.Std.parseCitation s with
  | .ok c => c
  | .error _ => default

/-- A case: the trace, and a `constexpr` function body that spells it,
returning an `int` the `static_assert` compares with `expected`. -/
def mk (name : String) (cite' : String) (trace : Trace) (body : String) (expected : Int)
    (m : Model := model) : ObjectCase :=
  let cpp := classes ++ s!"constexpr int f() \{\n{body}}\n" ++
    (if constant m trace then s!"static_assert(f() == {expected});\n"
     else s!"// the model expects the evaluation not to be a constant expression\nstatic_assert(f() == {expected});\n")
  { case :=
      { name, cite := cite cite', program := [], query := .raw cpp (constant m trace)
        source := "computed by Overload.Object.Machine.run; constant evaluation is the oracle"
        prelude := "" }
    trace, model := m }

/-- `int x; return x;`: erroneous, so not a constant expression. -/
def uninitRead : ObjectCase :=
  mk "object_uninit_read" "basic.indet#2"
    [.var "x" int, .addr "p" "x", .read "v" "p"]
    "  int x;\n  return x;\n" 0

/-- `int x; x = 1; return x;`: the profile rejects it, and it is fine. -/
def assignedBeforeRead : ObjectCase :=
  mk "object_assigned_before_read" "basic.indet#1"
    [.var "x" int, .addr "p" "x", .write "p" 1, .read "v" "p"]
    "  int x;\n  x = 1;\n  return x;\n" 1

/-- `Pair p{}; return p.a + p.b;`: aggregate initialization from an
empty list value-initializes every element. -/
def valueInitZero : ObjectCase :=
  mk "object_value_init_zero" "dcl.init.aggr#6"
    [.var "p" cPair (.braces []), .addr "pp" "p", .member "pa" "pp" 0, .read "a" "pa", .member "pb" "pp" 1,
     .read "b" "pb"]
    "  Pair p{};\n  return p.a + p.b;\n" 0

/-- `T t{}; return t.x;` with `T() {}`: the initializer runs a
constructor that leaves `x` alone. -/
def userCtorLeavesMember : ObjectCase :=
  mk "object_user_ctor_leaves_member" "dcl.init.general#8"
    [.var "t" cT .value, .addr "p" "t", .member "px" "p" 0, .read "v" "px"]
    "  T t{};\n  return t.x;\n" 0

/-- `U u{}; return u.s;`: the first member is active, the second is not. -/
def unionInactiveRead : ObjectCase :=
  mk "object_union_inactive_read" "class.union.general#2"
    [.var "u" cU .value, .addr "pu" "u", .member "ps" "pu" 1, .read "v" "ps"]
    "  U u{};\n  return u.s;\n" 0

/-- `U u{}; u.s = 3; return u.s;`: the assignment begins `s`'s lifetime. -/
def unionAssignmentActivates : ObjectCase :=
  mk "object_union_assignment_activates" "class.union.general#5"
    [.var "u" cU .value, .addr "pu" "u", .member "ps" "pu" 1, .write "ps" 3, .read "v" "ps"]
    "  U u{};\n  u.s = 3;\n  return u.s;\n" 3

/-- `C c{1}; std::destroy_at(&c); return c.i;`: outside its lifetime. -/
def destroyThenRead : ObjectCase :=
  mk "object_destroy_then_read" "basic.life#8"
    [.var "c" cC (.braces [1]), .addr "p" "c", .destroy "p", .member "pi" "p" 0, .read "v" "pi"]
    "  C c{1};\n  std::destroy_at(&c);\n  return c.i;\n" 1

/-- `std::destroy_at` twice: a destructor invoked for an object whose
lifetime has ended. -/
def doubleDestroy : ObjectCase :=
  mk "object_double_destroy" "class.dtor#18"
    [.var "c" cC (.braces [1]), .addr "p" "c", .destroy "p", .destroy "p"]
    "  C c{1};\n  std::destroy_at(&c);\n  std::destroy_at(&c);\n  return 0;\n" 0

/-- [basic.life]/10 with `std::construct_at`: a non-const complete object
replaced by one of the same type, read through the old pointer and by
name. -/
def transparentReplacement : ObjectCase :=
  mk "object_transparent_replacement" "basic.life#10"
    [.var "c" cC (.braces [1]), .addr "p" "c", .destroy "p", .placementNew "p2" cC "p" (.braces [2]),
     .member "pi" "p" 0, .read "v" "pi", .addr "p3" "c", .member "ci" "p3" 0, .read "w" "ci"]
    "  C c{1};\n  C* p = &c;\n  std::destroy_at(p);\n  std::construct_at(p, 2);\n  return p->i + c.i;\n" 4

/-- `E e{1}; std::destroy_at(&e);` and the block exits: the implicit
destructor call finds no object of the original type. -/
def implicitDestructor : ObjectCase :=
  mk "object_implicit_destructor" "basic.life#11"
    [.var "e" cE (.braces [1]), .addr "p" "e", .destroy "p", .endBlock]
    "  {\n    E e{1};\n    std::destroy_at(&e);\n  }\n  return 0;\n" 0

/-- The same with an `E` recreated before the block exits: fine. -/
def destroyRecreateBlockExit : ObjectCase :=
  mk "object_destroy_recreate_block_exit" "basic.life#11"
    [.var "e" cE (.braces [1]), .addr "p" "e", .destroy "p", .placementNew "p2" cE "p" (.braces [2]),
     .addr "p3" "e", .member "pe" "p3" 0, .read "v" "pe", .endBlock]
    "  int v;\n  {\n    E e{1};\n    std::destroy_at(&e);\n    std::construct_at(&e, 2);\n    v = e.e;\n  }\n  return v;\n" 2

/-- `int* p = new int; int v = *p; delete p;`: dynamic storage is
indeterminate. -/
def newIntUninit : ObjectCase :=
  mk "object_new_int_uninit" "basic.indet#1"
    [.newObject "p" int, .read "v" "p", .delete "p"]
    "  int* p = new int;\n  int v = *p;\n  delete p;\n  return v;\n" 0

/-- `int* p = new int(4); int v = *p; delete p;`: initialized. -/
def newIntInit : ObjectCase :=
  mk "object_new_int_init" "basic.indet#1"
    [.newObject "p" int (.scalar 4), .read "v" "p", .delete "p"]
    "  int* p = new int(4);\n  int v = *p;\n  delete p;\n  return v;\n" 4

/-- [ptr.launder]/6 in constant evaluation, with `std::allocator` for
the storage and `std::construct_at` for the objects: a const complete
`X` replaced by an `X`. The old pointer does not refer to the new
object; `std::launder` does. -/
def launderConstComplete (laundered : Bool) : ObjectCase :=
  let tail : Trace :=
    if laundered then [.launder "l" "p", .member "ln" "l" 0, .read "c" "ln", .destroy "l", .free "s"]
    else [.member "pn2" "p" 0, .read "c" "pn2", .destroy "s", .free "s"]
  let readC := if laundered then "std::launder(p)->n" else "p->n"
  let destroy := if laundered then "std::launder(p)" else "s"
  mk (if laundered then "object_launder_const_complete" else "object_const_complete_not_replaced")
    (if laundered then "ptr.launder#6" else "basic.life#9")
    ([ .malloc "s" 4, .cast "s0" (.const cX) "s", .placementNew "p" (.const cX) "s0" (.braces [3])
     , .member "pn" "p" 0, .read "a" "pn"
     , .placementNew "p2" cX "s" (.braces [5]) ] ++ tail)
    (s!"  std::allocator<X> al;\n  X* s = al.allocate(1);\n" ++
     "  const X* p = std::construct_at(static_cast<const X*>(s), 3);\n" ++
     "  const int a = p->n;\n" ++
     "  std::construct_at(s, 5);\n" ++
     s!"  const int c = {readC};\n" ++
     s!"  std::destroy_at({destroy});\n  al.deallocate(s, 1);\n  return a + c;\n") 8

/-- [ptr.launder]/5: a base class subobject replaced by a complete `B`.
The old pointer refers to the dead base subobject; `std::launder`
finds the new `B`. -/
def launderBase (laundered : Bool) : ObjectCase :=
  let tail : Trace :=
    if laundered then [.launder "l" "pb", .member "lb" "l" 0, .read "v" "lb"]
    else [.member "pbb" "pb" 0, .read "v" "pbb"]
  mk (if laundered then "object_launder_base_subobject" else "object_base_subobject_not_replaced")
    "ptr.launder#5"
    ([ .var "d" cD (.braces [1, 2]), .addr "pd" "d", .member "pb" "pd" 0
     , .placementNew "nb" cB "pb" (.braces [7]) ] ++ tail)
    ("  D d{1, 2};\n  B* pb = &d;\n  std::construct_at(pb, 7);\n" ++
     s!"  return {if laundered then "std::launder(pb)->b" else "pb->b"};\n") 7

/-! ### P4222R3's accepted traces (`Overload/Object/P4222.lean`) -/

/-- `U u{7}; return u.s;`: an initialized union whose inactive member is
read. The profile accepts (`P4222.unionInactive`). -/
def unionInitializedInactiveRead : ObjectCase :=
  mk "object_union_initialized_inactive_read" "class.union.general#2"
    [.var "u" cU (.braces [7]), .addr "pu" "u", .member "ps" "pu" 1, .read "v" "ps"]
    "  U u{7};\n  return u.s;\n" 0

/-- A base subobject destroyed and recreated as a complete `B`, then the
complete object's own member read (`P4222.baseReplaced`). -/
def baseDestroyedReplacedComplete : ObjectCase :=
  mk "object_base_destroyed_replaced_complete" "basic.life#2"
    [ .var "d" cD (.braces [1, 2]), .addr "pd" "d", .member "pb" "pd" 0
    , .destroy "pb", .placementNew "nb" cB "pb" (.braces [7])
    , .addr "pd2" "d", .member "pdd" "pd2" 1, .read "v" "pdd" ]
    "  D d{1, 2};\n  B* pb = &d;\n  std::destroy_at(pb);\n  std::construct_at(pb, 7);\n  return d.d;\n" 2

/-- [ptr.launder]/6 with the destructor call the profile requires before
the storage is reused, read through the old pointer
(`P4222.launderExample`). -/
def constCompleteDestroyedNotReplaced : ObjectCase :=
  mk "object_const_complete_destroyed_not_replaced" "basic.life#9"
    [ .malloc "s" 4, .cast "s0" (.const cX) "s", .placementNew "p" (.const cX) "s0" (.braces [3])
    , .member "pn" "p" 0, .read "a" "pn"
    , .destroy "p", .placementNew "p2" cX "s" (.braces [5])
    , .member "pn2" "p" 0, .read "c" "pn2", .destroy "s", .free "s" ]
    ("  std::allocator<X> al;\n  X* s = al.allocate(1);\n" ++
     "  const X* p = std::construct_at(static_cast<const X*>(s), 3);\n" ++
     "  const int a = p->n;\n  std::destroy_at(p);\n  std::construct_at(s, 5);\n" ++
     "  const int c = p->n;\n  std::destroy_at(s);\n  al.deallocate(s, 1);\n  return a + c;\n") 8

/-- `constexpr void destroy(C* p) { std::destroy_at(p); }` then
`C c{1}; destroy(&c); std::destroy_at(&c);`
(`Functions.calleeDestroysThenDestroy`). -/
def calleeDestroys : ObjectCase :=
  mk "object_callee_destroys" "class.dtor#18"
    [.var "c" cC (.braces [1]), .addr "p" "c", .call none "destroy" ["p"], .destroy "p"]
    "  C c{1};\n  destroy(&c);\n  std::destroy_at(&c);\n  return 0;\n" 0
    { model with functions := [{ name := "destroy", params := [("p", cC)], body := [.destroy "p"] }] }

/-- Every case. -/
def cases : List ObjectCase :=
  [ uninitRead, assignedBeforeRead, valueInitZero, userCtorLeavesMember
  , unionInactiveRead, unionAssignmentActivates
  , destroyThenRead, doubleDestroy, transparentReplacement
  , implicitDestructor, destroyRecreateBlockExit
  , newIntUninit, newIntInit
  , launderBase true, launderBase false
  , unionInitializedInactiveRead, baseDestroyedReplacedComplete, calleeDestroys ]

/-- The const complete object cases, `launderConstComplete` and
`constCompleteDestroyedNotReplaced`, are not emitted. They create a
`const X` with `std::construct_at(static_cast<const X*>(s), 3)`, which
libstdc++ 15 and 16 reject (`const void*` to `void*` in `construct_at`),
so on those libraries every compiler "agrees" with the model's
ill-formed expectation for the wrong reason, and the case that expects
well-formed fails. GCC 13 and Clang 18, with the older library, accepted
them; the finding in `docs/findings.md` rests on that run. Constant
evaluation has no other way to create a const complete object. -/
def constCases : List ObjectCase :=
  [launderConstComplete true, launderConstComplete false, constCompleteDestroyedNotReplaced]

/-- The cases the harness compiles. -/
def harnessCases : List Case := cases.map (·.case)

end Overload.Object.Emit
