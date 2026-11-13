-- Overload/Object/Construction.lean                                  -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Object.Functions

/-!
# Constructor bodies and the period of construction

A constructor with a body runs in two phases ([class.base.init]/15): the
elements in declaration order, each from its mem-initializer or by
default-initialization, then the body. The machine models the object as
*constructing* from the moment its storage is created
(`Life.constructing`, [class.cdtor]/3): a pointer to one of its members
may be formed, the members' lifetimes begin one at a time as each
initialization completes ([basic.life]/2), and the object's own lifetime
begins when the constructor returns ([class.base.init]/11).

Two consequences are the point of this module.

* **A mem-initializer can read a member that is not yet initialized.**
  The order is the declaration order whatever order the list is written
  in, so `W() : a(b), b(1) {}` reads `b` before its lifetime has begun,
  which is undefined ([basic.life]/8). Neither P4222R3 nor P4416R0 has a
  rule about the order of mem-initializers: P4416R0 says members are
  initialized "at the start of the constructor's compound-statement"
  ([profiles.init.class]/1), which is true of the body and not of the
  list. The profile accepts the trace.
* **An `[[uninit]]` member initialized by the constructor stays
  uninitialized outside it** ([profiles.init.class]/2). A program that
  reads it after construction is defined and rejected.
-/

namespace Overload.Object.Construction

open Machine P4222

private def int : Ty := .named "int"
private def cW : Ty := .named "W"
private def cZ : Ty := .named "Z"
private def cQ : Ty := .named "Q"
private def cR : Ty := .named "R"

/-- `struct W { int a; int b; W() : a(b), b(1) {} };`
`struct Z { int a; int b; Z() : a(1), b(a) {} };`
`struct Q { int p; int x; Q() : x(7) { p = 5; } };`
`struct R { int m; int n; R() : n(2) { auto v = m; } };` -/
def model : Model :=
  { program :=
      [ .class "W", .special cW { kind := .defaultCtor }
      , .member cW { name := "a", ty := int }, .member cW { name := "b", ty := int }
      , .class "Z", .special cZ { kind := .defaultCtor }
      , .member cZ { name := "a", ty := int }, .member cZ { name := "b", ty := int }
      , .class "Q", .special cQ { kind := .defaultCtor }
      , .member cQ { name := "p", ty := int }, .member cQ { name := "x", ty := int }
      , .class "R", .special cR { kind := .defaultCtor }
      , .member cR { name := "m", ty := int }, .member cR { name := "n", ty := int } ]
    ctors :=
      [ { cls := cW, memInits := [(0, .fromMember 1), (1, .value (.scalar 1))] }
      , { cls := cZ, memInits := [(0, .value (.scalar 1)), (1, .fromMember 0)] }
      , { cls := cQ, memInits := [(1, .value (.scalar 7))], body := [.member "pp" "this" 0, .write "pp" 5] }
      , { cls := cR, memInits := [(1, .value (.scalar 2))], body := [.member "pm" "this" 0, .read "v" "pm"] } ] }

/-- The model with only the constructor of one class, so that the
constructor checks of the others do not report. -/
def only (c : Ty) : Model :=
  let keep : Decl → Bool
    | .class n .. => c == .named n
    | .member t _ => t == c
    | .special t _ => t == c
    | _ => true
  { model with ctors := model.ctors.filter (·.cls == c), program := model.program.filter keep }

/-- Define an object of class `c` and read its element `i`. -/
def readElement (c : Ty) (i : Nat) : Trace :=
  [.var "o" c, .addr "p" "o", .member "pe" "p" i, .read "v" "pe"]

def none' : Annotations := { rules := .wording }
def marked (c : Ty) (i : Nat) : Annotations := { rules := .wording, uninitMembers := [(c, i)] }

/-! ## The Standard: order and lifetime -/

/-- `W w; auto v = w.a;` reads `b` before it is initialized: the
constructor itself is undefined ([class.base.init]/15, [basic.life]/8). -/
@[std example "class.base.init#17" "class.base.init#15"]
theorem w_reads_member_before_init : run model (readElement cW 0) = .undefined .outsideLifetime := by decide

/-- `Z() : a(1), b(a)` reads `a` after it is initialized: defined. -/
theorem z_reads_member_after_init :
    ((run model (readElement cZ 1)).state?.bind (·.val? "v")) = some (.int 1) := by decide

/-- The mem-initializer list's order does not matter: elements are
initialized in declaration order ([class.base.init]/15). `W` and `Z`
with their lists reversed behave as written. -/
def reversed (cd : CtorDef) : Model :=
  { model with ctors := [ { cd with memInits := cd.memInits.reverse } ] }

@[std theorem "class.base.init#15"]
theorem mem_init_order_is_declaration_order :
    run (reversed (model.ctorOf? cW).get!) (readElement cW 0) = .undefined .outsideLifetime ∧
    ((run (reversed (model.ctorOf? cZ).get!) (readElement cZ 1)).state?.bind (·.val? "v")) = some (.int 1) := by
  decide

/-- The object is within its lifetime once the constructor returns, and
its members are. -/
@[std theorem "class.base.init#11" "basic.life#2"]
theorem alive_after_constructor :
    ((run model [.var "o" cZ]).state?.bind fun s => (s.name? "o").map s.alive) = some true := by decide

/-- A member that has a mem-initializer is initialized, one that does not
and is a scalar is left as storage had it, here erroneous: `R() : n(2) {
auto v = m; }` reads an erroneous `m` in its body, which is erroneous
behaviour ([basic.indet]/2), and `n` is 2. -/
@[std example "basic.indet#2" "class.base.init#15"]
theorem r_body_reads_unset_member :
    (run model [.var "o" cR]).isErroneous = true ∧
    ((run model (readElement cR 1)).state?.bind (·.val? "v")) = some (.int 2) := by
  decide

/-- The assignment in `Q`'s body sets `p`; `x` comes from the list. -/
theorem q_body_assignment :
    ((run model (readElement cQ 0)).state?.bind (·.val? "v")) = some (.int 5) ∧
    ((run model (readElement cQ 1)).state?.bind (·.val? "v")) = some (.int 7) := by
  decide

/-! ## The profile: P4416R0 [profiles.init.class] -/

/-- `W() : a(b), b(1)`: nothing in the wording orders the list, the
profile accepts, the constructor is undefined. G1, "every object is
initialized before it is used", fails inside a constructor that
initializes every member. -/
theorem w_accepted_undefined :
    accepts (only cW) none' (readElement cW 0) = true ∧ hazard (only cW) (readElement cW 0) = true := by decide

/-- `Z`: accepted and defined; the profile and the Standard agree. -/
theorem z_accepted_defined :
    accepts (only cZ) none' (readElement cZ 1) = true ∧ hazard (only cZ) (readElement cZ 1) = false := by decide

/-- `Q() : x(7) { p = 5; }` with `p` not marked: [profiles.init.decl]/1,
`p` is left uninitialized by the list and must be `[[uninit]]`. -/
theorem q_unmarked_rejected :
    check (only cQ) none' [.var "o" cQ] = [.constructorLeavesMember cQ 0] := by decide

/-- With `p` marked `[[uninit]]` the constructor passes: the assignment in
the body initializes it ([profiles.init.class]/1 note). -/
theorem q_marked_constructor_accepted : ctorViolations (only cQ) (marked cQ 0) = [] := by decide

/-- But `Q q; auto v = q.p;` outside the constructor is rejected: a
marked member of an initialized object is uninitialized
([profiles.init.class]/2), and the read is defined and gives 5. The
paper's remedy is `now_init` or a placeholder initializer. -/
theorem q_read_outside_rejected :
    check (only cQ) (marked cQ 0) (readElement cQ 0) = [.readUninit "pe"] ∧
    hazard (only cQ) (readElement cQ 0) = false ∧
    ((run (only cQ) (readElement cQ 0)).state?.bind (·.val? "v")) = some (.int 5) := by
  decide

/-- Reading the marked member inside the constructor before assigning it
is rejected and erroneous: `R` with `m` marked. -/
theorem r_body_read_agree :
    check (only cR) (marked cR 0) [.var "o" cR] = [.readUninit "pm"] ∧ hazard (only cR) [.var "o" cR] = true := by
  decide

/-- A marked member must not be named in a mem-initializer
([profiles.init.decl]/2), and a mem-initializer that reads one reads an
uninitialized object. `Z` with `a` marked is both. -/
theorem marked_member_named :
    ctorViolations (only cZ) (marked cZ 0) = [.uninitMemberNamed cZ 0, .memInitReadsUninit cZ 0] := by decide

/-- The table for constructors. -/
def acceptedHazards : List Trace := [readElement cW 0]

theorem accepted_hazards : acceptedHazards.all (fun t => accepts (only cW) none' t && hazard (only cW) t) = true := by decide

end Overload.Object.Construction
