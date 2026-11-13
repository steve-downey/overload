-- Overload/Object/Profile.lean                                       -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Object.Machine

/-!
# The definition rule of the initialization profile against the object model

The first rule of P4222R3's initialization profile is a rule on the
source: every variable is initialized at its definition, with an
attribute as the opt-out (§4.1; the paper spells it `[[uninit]]`, this
module takes `[[indeterminate]]` as the mark on the fragment's
definitions). `Overload/Object/P4222.lean` transcribes the paper's full
rule set; this module keeps the definition rule alone, which is what
the comparison needs to show that the rule's subject, variables, is not
the hazard's, objects. The object model lets the rule be stated against the thing
it is meant to prevent, a read that produces an indeterminate or
erroneous value, or any other undefined behaviour of the trace, and the
two compared. Both directions fail, and each failure is a concrete trace
(`decisions.md#initialization-profile`).

* **Not sound.** Traces the profile accepts have the hazard: a `new int`
  read before assignment; a class whose user-provided constructor leaves
  a member alone, under `T t{};`; a variable marked `[[indeterminate]]`;
  `start_lifetime_as` over indeterminate storage; a union whose inactive
  member is read; an initialized variable whose object's lifetime has
  ended. The rule speaks of variables and their initializers; the hazard
  is about objects, bytes and lifetimes, and most objects are not
  variables.
* **Not complete.** Traces the profile rejects have no hazard: a scalar
  assigned before it is read; a byte buffer filled by a system call
  before it is read; a static variable, which is zero-initialized.

The last theorems separate the two notions the rule conflates. An object
can be within its lifetime with an erroneous value: `int x;` begins the
lifetime of `x` by vacuous initialization ([basic.life]/2), and the
value is erroneous ([basic.indet]/1). And an object can hold a
determinate value outside its lifetime, when reading it is undefined
all the same.
-/

namespace Overload.Object

open Machine

namespace Profile

/-- The initialization profile's rule on one operation: a definition
without an initializer is rejected, unless the variable is marked
`[[indeterminate]]`. Everything that is not a definition passes, since
the rule is about variables. -/
def accepts : Op → Bool
  | .var _ _ .default indet _ => indet
  | .staticVar _ _ .default => false
  | _ => true

/-- The profile accepts a trace when it accepts every operation. -/
def acceptsTrace (t : Trace) : Bool := t.all accepts

/-- The hazard the profile is meant to prevent, stated on the execution:
the trace has undefined behaviour or erroneous behaviour. -/
def hazard (m : Model) (t : Trace) : Bool :=
  match run m t with
  | .undefined _ | .erroneous _ _ => true
  | _ => false

/-- An uninitialized read in particular: the trace reads an indeterminate
or erroneous value. -/
def uninitializedRead (m : Model) (t : Trace) : Bool :=
  match run m t with
  | .undefined .indeterminateValue | .erroneous _ _ => true
  | _ => false

private def int : Ty := .named "int"
private def uchar : Ty := .named "unsigned char"
private def short : Ty := .named "short"
private def cT : Ty := .named "T"
private def cPair : Ty := .named "Pair"
private def cU : Ty := .named "U"

/-- `struct T { T() {} int x; }; struct Pair { short a; short b; };
union U { int i; short s; };` -/
def model : Model :=
  { program :=
      [ .class "T", .special cT { kind := .defaultCtor }, .member cT { name := "x", ty := int }
      , .class "Pair", .member cPair { name := "a", ty := short }, .member cPair { name := "b", ty := short } ]
    unions := [("U", [{ name := "i", ty := int }, { name := "s", ty := short }])] }

/-! ## Not sound: accepted traces with the hazard -/

/-- `int* p = new int; auto v = *p;` -/
def newInt : Trace := [.newObject "p" int, .read "v" "p"]

/-- `T t{}; auto v = t.x;` with `T() {}`: the initializer is there, the
constructor runs, and `x` is left erroneous. -/
def userProvidedCtor : Trace := [.var "t" cT .value, .addr "p" "t", .member "px" "p" 0, .read "v" "px"]

/-- `int x [[indeterminate]]; auto v = x;` -/
def indeterminateAttr : Trace := [.var "x" int .default true, .addr "p" "x", .read "v" "p"]

/-- `void* m = malloc(4); auto* p = std::start_lifetime_as<Pair>(m); auto v = p->a;` -/
def startLifetimeAsIndeterminate : Trace :=
  [.malloc "m" 4, .startLifetimeAs "p" cPair "m", .member "pa" "p" 0, .read "v" "pa"]

/-- `U u{}; auto v = u.s;`: the union is initialized, its first member
active, and the read of the other member undefined. -/
def inactiveUnionMember : Trace := [.var "u" cU .value, .addr "pu" "u", .member "ps" "pu" 1, .read "v" "ps"]

/-- `int x = 1; (&x)->~int(); auto v = x;`: initialized, then outside
its lifetime. -/
def initializedThenDestroyed : Trace := [.var "x" int (.scalar 1), .addr "p" "x", .destroy "p", .read "v" "p"]

/-- The accepted traces with the hazard. -/
def acceptedHazards : List Trace :=
  [newInt, userProvidedCtor, indeterminateAttr, startLifetimeAsIndeterminate, inactiveUnionMember,
   initializedThenDestroyed]

/-- The profile accepts each. -/
theorem accepted_hazards_accepted : acceptedHazards.all acceptsTrace = true := by decide

/-- Each has the hazard. -/
theorem accepted_hazards_hazard : acceptedHazards.all (hazard model) = true := by decide

/-- The profile is not sound: an accepted trace has the hazard. -/
theorem not_sound : ∃ t, acceptsTrace t = true ∧ hazard model t = true := ⟨newInt, by decide⟩

/-- The first four are uninitialized reads, the hazard the rule names. -/
theorem accepted_uninitialized_reads :
    [newInt, userProvidedCtor, indeterminateAttr, startLifetimeAsIndeterminate].all (uninitializedRead model) = true := by
  decide

/-- `new int` is read as an indeterminate value: undefined, not erroneous,
since dynamic storage has indeterminate bytes. -/
@[std example "basic.indet#1"]
theorem new_int_undefined : run model newInt = .undefined .indeterminateValue := by decide

/-- `T t{}` with `T() {}` reads `x` as an erroneous value
([dcl.attr.indet]/3 has the same class with `[[indeterminate]]`). -/
@[std example "dcl.attr.indet#3" "dcl.init.general#8"]
theorem user_provided_ctor_erroneous : (run model userProvidedCtor).isErroneous = true := by decide

/-! ## Not complete: rejected traces without the hazard -/

/-- `int x; x = 1; auto v = x;` -/
def assignedBeforeRead : Trace := [.var "x" int, .addr "p" "x", .write "p" 1, .read "v" "p"]

/-- `unsigned char buf[4]; read(fd, buf, 4); auto v = *reinterpret_cast<int*>(buf);` -/
def bufferFilled : Trace :=
  [.var "buf" uchar .default false 4, .addr "b" "buf", .storeBytes "b" [1, 0, 0, 0], .cast "p" int "b", .read "v" "p"]

/-- `static int x; auto v = x;`: zero-initialized. -/
def staticZero : Trace := [.staticVar "x" int, .addr "p" "x", .read "v" "p"]

/-- The rejected traces without the hazard. -/
def rejectedSafe : List Trace := [assignedBeforeRead, bufferFilled, staticZero]

theorem rejected_safe_rejected : rejectedSafe.all (fun t => !acceptsTrace t) = true := by decide

theorem rejected_safe_defined : rejectedSafe.all (fun t => !hazard model t) = true := by decide

/-- The profile is not complete: a rejected trace has no hazard. -/
theorem not_complete : ∃ t, acceptsTrace t = false ∧ hazard model t = false := ⟨assignedBeforeRead, by decide⟩

/-! ## Lifetime is not initialization -/

/-- After `int x;`, the object `x` names is within its lifetime. -/
@[std theorem "basic.life#2"]
theorem vacuous_initialization_begins_lifetime :
    ((run model [.var "x" int]).state?.bind fun s => (s.name? "x").map s.alive) = some true := by
  decide

/-- And its value is erroneous: within its lifetime, uninitialized. -/
@[std theorem "basic.indet#1"]
theorem vacuous_initialization_erroneous_value :
    ((run model [.var "x" int, .addr "p" "x", .read "v" "p"]).state?.bind (·.val? "v")) = some .erroneous := by
  decide

/-- After `int x = 1; (&x)->~int();` the bytes of `x` still hold 1, and
reading `x` is undefined: a determinate value outside a lifetime. -/
@[std theorem "basic.life#8"]
theorem determinate_outside_lifetime :
    ((run model [.var "x" int (.scalar 1), .addr "p" "x", .destroy "p"]).state?.map fun s =>
      bytesAt s 0 0 4) = some (encode 1 4) ∧
    run model initializedThenDestroyed = .undefined .outsideLifetime := by
  decide

end Profile

end Overload.Object
