-- Overload/Object/P4416.lean                                         -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Object.P4222

/-!
# P4416R0, the proposed wording for the initialization profile

Wong and Stroustrup's P4416R0 (23 October 2026) is the working-draft
wording for P4222R3: a clause [profiles.init] with the guarantees
G1 to G5, the terms (initialization state, "refers to uninitialized
objects"), the every-path analysis, the rules by subclause, four
attributes and the library annotations. It is more precise than the
design paper and differs from it where the checker has switches
(`P4222.Rules.wording`): no exception for reading bytes
([profiles.init.use]/1), byte stores into an uninitialized array are
uses ([profiles.init.use]/(1.3) and its example), `memcpy` is not an
initialization (the drafting note under [profiles.init.terms]/4),
arguments to unannotated functions must refer to initialized objects
([profiles.init.ref]/4), and an automatic object of a type that is not
trivially destructible must be initialized where its scope ends
([profiles.init.life]/2).

This module reproduces the wording's own examples, then states what the
wording changes in the comparison with the object model: the design
paper's `start_lifetime_as` dilemma becomes a different pair of
theorems, the delete-expression opens a hole in G2, and `memcpy` and
byte stores into `[[uninit]]` buffers become rejected-and-defined. One
of the wording's examples is ill-formed by its own rules
(`ref8_now_init_after_construct_at`).
-/

namespace Overload.Object.P4416

open Machine P4222

private def int : Ty := .named "int"
private def uchar : Ty := .named "unsigned char"
private def short : Ty := .named "short"
private def cX : Ty := .named "X"
private def cC : Ty := .named "C"
private def cE : Ty := .named "E"
private def cS : Ty := .named "S"
private def cPair : Ty := .named "Pair"
private def cPoint : Ty := .named "Point"
private def cT : Ty := .named "T"
private def cU : Ty := .named "U"
private def cB : Ty := .named "B"
private def cD : Ty := .named "D"

/-- P4222's classes, with `struct E { int e; ~E(); }`, the type that is
not trivially destructible, and `struct S { int x; T s; }`, the
wording's `S` with `T` standing for `std::string`: a member whose
default constructor is user-provided. -/
def model : Model :=
  { program :=
      [ .class "X", .member cX { name := "n", ty := int }
      , .class "C", .member cC { name := "i", ty := int }
      , .class "E", .special cE { kind := .dtor }, .member cE { name := "e", ty := int }
      , .class "Pair", .member cPair { name := "a", ty := short }, .member cPair { name := "b", ty := short }
      , .class "Point", .member cPoint { name := "x", ty := int }, .member cPoint { name := "y", ty := int }
      , .class "T", .special cT { kind := .defaultCtor }, .member cT { name := "x", ty := int }
      , .class "S", .member cS { name := "x", ty := int }, .member cS { name := "s", ty := cT }
      , .class "B", .member cB { name := "b", ty := int }
      , .class "D" [cB], .member cD { name := "d", ty := int } ]
    unions := [("U", [{ name := "i", ty := int }, { name := "s", ty := short }])]
    ctorInits := [(cT, [(0, 0)])] }

/-- The wording's rules, no `[[uninit]]`. -/
def w : Annotations := { rules := .wording }

/-- The wording's rules with these variables `[[uninit]]`. -/
def wu (xs : List String) : Annotations := { rules := .wording, uninit := xs }

/-! ## [profiles.init.decl]/6 -/

/-- `int glob; // OK: zero-initialized`, `int glob2 [[uninit]]; // error`. -/
theorem decl6_glob :
    accepts model w [.staticVar "glob" int] = true ∧
    check model (wu ["glob2"]) [.staticVar "glob2" int] = [.initializedAndUninit "glob2"] := by
  decide

/-- `int loc; // error`, `int loc2 [[uninit]]; // OK`, `int loc4 [[uninit]] = 4; // error`. -/
theorem decl6_loc :
    check model w [.var "loc" int] = [.uninitializedNotMarked "loc"] ∧
    accepts model (wu ["loc2"]) [.var "loc2" int] = true ∧
    check model (wu ["loc4"]) [.var "loc4" int (.scalar 4)] = [.initializedAndUninit "loc4"] := by
  decide

/-- `S s3; // error: s3.x would be uninitialized`, `S s4 [[uninit]]; //
error: s4.s would be initialized`. -/
theorem decl6_s :
    check model w [.var "s3" cS] = [.uninitializedNotMarked "s3"] ∧
    check model (wu ["s4"]) [.var "s4" cS] = [.initializedAndUninit "s4"] := by
  decide

/-! ## [profiles.init.use]/5 -/

/-- `int i [[uninit]]; int j = i; // error; i = 7; int k = i; // OK`. -/
theorem use5_scalar :
    check model (wu ["i"]) [.var "i" int, .addr "p" "i", .read "j" "p"] = [.readUninit "p"] ∧
    accepts model (wu ["i"]) [.var "i" int, .addr "p" "i", .write "p" 7, .read "k" "p"] = true := by
  decide

/-- `P p [[uninit]]; p.x = 1; // error (1.3)`, then
`std::construct_at(&p, 1, 2); // OK`. -/
theorem use5_aggregate :
    check model (wu ["p"]) [.var "p" cPoint, .addr "pp" "p", .member "px" "pp" 0, .write "px" 1] =
      [.memberAssignment "px"] ∧
    accepts model (wu ["p"]) [.var "p" cPoint, .addr "pp" "p", .placementNew "p2" cPoint "pp" (.braces [1, 2]),
      .member "px" "p2" 0, .read "v" "px"] = true := by
  decide

/-- `U u [[uninit]]; u.x = 9; // error (1.3)`. -/
theorem use5_union :
    check model (wu ["u"]) [.var "u" cU, .addr "pu" "u", .member "pi" "pu" 0, .write "pi" 9] =
      [.memberAssignment "pi"] := by
  decide

/-- `std::byte buf [[uninit]] [64]; buf[0] = std::byte{0}; // error`. The
design paper's §4.8 says the opposite of this store. -/
theorem use5_byte_store :
    check model (wu ["buf"]) [.var "buf" uchar .default false 64, .addr "b" "buf", .storeBytes "b" [0]] =
      [.memberAssignment "b"] := by
  decide

/-! ## [profiles.init.life]/4, `k(X* p [[ref_to_uninit]])` -/

/-- `construct_at(p); // OK; construct_at(p); // error; destroy_at(p); //
OK; destroy_at(p); // error`, with `p` from `new C` as the pointer that
refers to uninitialized objects. -/
theorem life4_k :
    check model w [.newObject "p" cC, .placementNew "p1" cC "p" (.braces [1]), .placementNew "p2" cC "p" (.braces [2]),
      .destroy "p", .destroy "p"] = [.constructTwice "p", .destroyTwice "p"] := by
  decide

/-! ## [profiles.init.ref]/8 -/

/-- `int* s [[ref_to_uninit]] = buffer(4); int y = s[0]; // error`. -/
theorem ref8_read_uninit : check model w [.newObject "s" int, .read "y" "s"] = [.readUninit "s"] := by decide

/-- `std::construct_at(s, 1); // OK` then `int* t = std::now_init(s); //
OK: t refers to initialized objects`. By [profiles.init.terms]/(4.5) a
call to `now_init` is an initialization of the object `s` designates,
and by [profiles.init.life]/1 an initialization shall not be applied to
an initialized object, which `*s` is after `construct_at`. The example
is ill-formed by the wording's own rules; the intent, converting the
pointer's marking, needs `now_init` taken out of (4.5) or exempted in
[profiles.init.life]/1. -/
theorem ref8_now_init_after_construct_at :
    check model w [.newObject "s" int, .placementNew "s1" int "s" (.scalar 1), .nowInit "t" "s"] =
      [.nowInitOfInitialized "s"] := by
  decide

/-! ## What the wording changes against the object model -/

/-- `std::start_lifetime_as` under the wording: its parameter is
unannotated, so storage from `malloc` cannot be passed to it
([profiles.init.ref]/4); the design paper's unsound reading is closed. -/
theorem start_lifetime_as_malloc_rejected :
    check model w P4222.startLifetimeAsIndeterminate = [.uninitArgument "m"] := by decide

/-- And its primary use, bytes in initialized storage, is accepted and
defined, closing the annotated reading's incompleteness. -/
theorem start_lifetime_as_defined_accepted :
    accepts model w P4222.startLifetimeAsDefined = true ∧ hazard model P4222.startLifetimeAsDefined = false := by
  decide

/-- But `start_lifetime_as<Pair>(&x)` ends the lifetime of `x`
([basic.life]/2), and the wording keeps `x` initialized, so `auto v = x;`
afterwards is accepted and undefined. -/
def startLifetimeAsEndsOld : Trace :=
  [.var "x" int (.scalar 1), .addr "p" "x", .startLifetimeAs "r" cPair "p", .read "v" "p"]

theorem start_lifetime_as_ends_old :
    accepts model w startLifetimeAsEndsOld = true ∧ run model startLifetimeAsEndsOld = .undefined .outsideLifetime := by
  decide

/-- A delete-expression is not a destruction ([profiles.init.terms]/5),
so `std::destroy_at(p); delete p;` is accepted: G2, "no object is
destroyed while it is not initialized", does not see the destructor the
delete-expression invokes, which [class.dtor]/18 makes undefined. -/
def destroyThenDelete : Trace := [.newObject "p" cC (.braces [1]), .destroy "p", .delete "p"]

theorem destroy_then_delete :
    accepts model w destroyThenDelete = true ∧ run model destroyThenDelete = .undefined .destructorOutsideLifetime := by
  decide

/-- `int* p = new int(1); delete p; auto v = *p;`: accepted, undefined,
and the invalidation profile's to catch; listed so the boundary is a
theorem. -/
def deleteThenRead : Trace := [.newObject "p" int (.scalar 1), .delete "p", .read "v" "p"]

theorem delete_then_read :
    accepts model w deleteThenRead = true ∧ run model deleteThenRead = .undefined .invalidPointer := by decide

/-- A zero-initialized byte buffer, filled, read as a `Pair`, filled
again, read as an `int`: every store is into initialized memory, so the
wording accepts; the second read finds no `int` ([intro.object]/13). -/
def bufferReuseInitialized : Trace :=
  [ .var "buf" uchar .value false 8, .addr "b" "buf", .storeBytes "b" [1, 0, 2, 0]
  , .cast "q" cPair "b", .member "qa" "q" 0, .read "v" "qa"
  , .storeBytes "b" [9, 0, 0, 0], .cast "r" int "b", .read "w" "r" ]

theorem buffer_reuse_initialized :
    accepts model w bufferReuseInitialized = true ∧ run model bufferReuseInitialized = .undefined .typeInaccessible := by
  decide

/-- `int x [[uninit]]; int y = 1; std::memcpy(&x, &y, 4); auto v = x;`:
rejected twice over, since `memcpy` is not an initialization, so its
unannotated parameter refuses `&x` and the read finds `x` uninitialized;
defined, and `x` holds 1 ([cstring.syn]/3,
[basic.types.general]/2). The drafting note under
[profiles.init.terms]/4 records the omission. -/
def memcpyInit : Trace :=
  [.var "x" int, .addr "px" "x", .var "y" int (.scalar 1), .addr "py" "y", .memcpy "px" "py" 4, .read "v" "px"]

theorem memcpy_init :
    check model (wu ["x"]) memcpyInit = [.uninitArgument "px", .readUninit "px"] ∧ hazard model memcpyInit = false ∧
    ((run model memcpyInit).state?.bind (·.val? "v")) = some (.int 1) := by
  decide

/-- `unsigned char buf [[uninit]] [8];` filled byte by byte, then read as
a `Pair`: rejected at the first store ([profiles.init.use]/(1.3)); defined,
the buffer's creation having implicitly created the `Pair`
([intro.object]/16). The design paper's §4.8 relies on exactly this fill,
through a `[[ref_to_uninit]]` function. -/
def byteFill : Trace :=
  [.var "buf" uchar .default false 8, .addr "b" "buf", .storeBytes "b" [1, 0, 2, 0], .cast "q" cPair "b",
   .member "qa" "q" 0, .read "v" "qa"]

theorem byte_fill :
    accepts model (wu ["buf"]) byteFill = false ∧ hazard model byteFill = false := by decide

/-- `E e [[uninit]]; }` with `~E()` user-provided: rejected by
[profiles.init.life]/2; defined, since `E e;` is vacuous initialization
and the destructor runs on an object within its lifetime. The rule
exists for G4 alone, as the wording's table says. -/
def uninitScopeExit : Trace := [.var "e" cE, .endBlock]

theorem uninit_scope_exit :
    check model (wu ["e"]) uninitScopeExit = [.uninitAtScopeExit "e"] ∧ hazard model uninitScopeExit = false := by
  decide

/-- With `std::construct_at(&e, 1)` before the exit: accepted and defined. -/
theorem uninit_scope_exit_constructed :
    accepts model (wu ["e"]) [.var "e" cE, .addr "p" "e", .placementNew "p2" cE "p" (.braces [1]), .endBlock] = true ∧
    hazard model [.var "e" cE, .addr "p" "e", .placementNew "p2" cE "p" (.braces [1]), .endBlock] = false := by
  decide

/-- And `E e{1}; std::destroy_at(&e); }`: rejected and undefined
([basic.life]/11); here the rule and the Standard agree. -/
theorem destroyed_scope_exit :
    check model w [.var "e" cE (.braces [1]), .addr "p" "e", .destroy "p", .endBlock] = [.uninitAtScopeExit "e"] ∧
    run model [.var "e" cE (.braces [1]), .addr "p" "e", .destroy "p", .endBlock] = .undefined .implicitDestructor := by
  decide

/-! ## The table under the wording -/

/-- Accepted and undefined. -/
def acceptedHazards : List Trace :=
  [ P4222.launderExample, P4222.baseReplaced, P4222.unionInactive, P4222.typePun
  , startLifetimeAsEndsOld, destroyThenDelete, deleteThenRead, bufferReuseInitialized ]

theorem accepted_hazards : acceptedHazards.all (fun t => accepts model w t && hazard model t) = true := by decide

/-- Rejected and defined. -/
def rejectedSafe : List (Annotations × Trace) :=
  [ (wu ["p"], P4222.pointAssigned), (wu ["u"], P4222.unionAssigned), (w, P4222.constructOverLive)
  , (wu ["x"], memcpyInit), (wu ["buf"], byteFill), (wu ["e"], uninitScopeExit) ]

theorem rejected_safe : rejectedSafe.all (fun (a, t) => !accepts model a t && !hazard model t) = true := by decide

/-- G1, "every object is initialized before it is used", does not hold
on the fragment under the wording. -/
theorem guarantee_fails : ∃ t, accepts model w t = true ∧ hazard model t = true :=
  ⟨P4222.unionInactive, by decide⟩

end Overload.Object.P4416
