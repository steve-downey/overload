-- Overload/Object/Functions.lean                                     -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Object.P4416

/-!
# The initialization profile across function calls

Both papers make the analysis local to a function body: a call affects
the caller's view of an argument only through the attributes on the
callee's declaration (P4222R3 §1.5, P4416R0 [profiles.init.general]/3,
[profiles.init.analysis]/1). The attributes say that a parameter refers
to uninitialized objects (`[[ref_to_uninit]]`), that the callee
initializes it (`[[must_init]]`, or `[[now_init]]` on the function), and
that a result refers to uninitialized objects. There is no attribute
for the other direction, a callee that destroys what it is passed: the
wording's drafting note under [dcl.attr.nowinit] says "there is no
now_uninit". With functions in the machine (`Op.call`, `FunDef`), the
theorems here run the callee and compare.

* `[[must_init]]` works as specified: a body that initializes passes,
  one that does not is the violation, and the caller may read.
* `[[ref_to_uninit]]` on a result works as specified.
* A callee that destroys through a plain parameter is accepted, since
  its parameter refers to initialized objects and a destruction of an
  initialized object is fine, and the caller, told nothing, destroys
  again or reads: G2 and G1 fail across the call.
* `[[now_init]]` is the declared hole, and the theorem says so.
-/

namespace Overload.Object.Functions

open Machine P4222

private def int : Ty := .named "int"
private def uchar : Ty := .named "unsigned char"
private def cX : Ty := .named "X"
private def cC : Ty := .named "C"

/-- `void destroy(C* p) { std::destroy_at(p); }`,
`void init(int* p [[must_init]]) { *p = 1; }`,
`void leave(int* p [[must_init]]) {}`,
`int read_fn [[now_init]] (unsigned char* p [[ref_to_uninit]]) {}`,
`int* alloc [[ref_to_uninit]] () { return new int; }`,
`int* alloc_bad() { return new int; }`,
`void reset(const X* p) { std::destroy_at(p); std::construct_at(const_cast<X*>(p), 5); }`,
`int* local() { int x = 1; return &x; }`. -/
def model : Model :=
  { program :=
      [ .class "X", .member cX { name := "n", ty := int }
      , .class "C", .member cC { name := "i", ty := int } ]
    functions :=
      [ { name := "destroy", params := [("p", cC)], body := [.destroy "p"] }
      , { name := "init", params := [("p", int)], body := [.write "p" 1] }
      , { name := "leave", params := [("p", int)], body := [] }
      , { name := "read_fn", params := [("p", uchar)], body := [] }
      , { name := "alloc", body := [.newObject "r" int], ret := some "r" }
      , { name := "alloc_bad", body := [.newObject "r" int], ret := some "r" }
      , { name := "reset", params := [("p", .const cX)]
          body := [.destroy "p", .cast "q" cX "p", .placementNew "p2" cX "q" (.braces [5])] }
      , { name := "local", body := [.var "x" int (.scalar 1), .addr "r" "x"], ret := some "r" } ] }

/-- The annotations: `init` and `leave` take `[[must_init]]`, `read_fn`
is `[[now_init]]` with a `[[ref_to_uninit]]` parameter, `alloc` returns
`[[ref_to_uninit]]`; `destroy`, `alloc_bad`, `reset` and `local` are
unannotated. -/
def sigs : List FunSig :=
  [ { name := "init", params := [.mustInit] }
  , { name := "leave", params := [.mustInit] }
  , { name := "read_fn", params := [.refToUninit], nowInit := true }
  , { name := "alloc", retRefToUninit := true, ret := int }
  , { name := "alloc_bad", ret := int }
  , { name := "local", ret := int } ]

def w : Annotations := { functions := sigs, rules := .wording }
def wu (xs : List String) : Annotations := { w with uninit := xs }

/-- The model's function bodies, checked on their own: `leave` fails its
`[[must_init]]` obligation and `alloc_bad` returns a pointer to
uninitialized objects without saying so; every other body passes. -/
theorem bodies :
    functionViolations model w = [.mustInitNotInitialized "leave" "p", .returnMarkMismatch "alloc_bad"] := by
  decide

/-- The accepted bodies alone. -/
def ok : Annotations := { w with functions := sigs.filter fun sg => sg.name != "leave" && sg.name != "alloc_bad" }
def okModel : Model := { model with functions := model.functions.filter fun fd => fd.name != "leave" && fd.name != "alloc_bad" }

theorem ok_bodies : functionViolations okModel ok = [] := by decide

/-! ## As specified -/

/-- `int x [[uninit]]; init(&x); auto v = x;`: accepted, defined, reads 1. -/
def mustInitWorks : Trace := [.var "x" int, .addr "p" "x", .call none "init" ["p"], .read "v" "p"]

theorem must_init_works :
    accepts okModel { ok with uninit := ["x"] } mustInitWorks = true ∧ hazard okModel mustInitWorks = false ∧
    ((run okModel mustInitWorks).state?.bind (·.val? "v")) = some (.int 1) := by
  decide

/-- `int x = 0; init(&x);`: an initialized argument to a `[[must_init]]`
parameter is rejected (P4416R0 [profiles.init.ref]/4). -/
theorem must_init_initialized_argument :
    check okModel ok [.var "x" int (.scalar 0), .addr "p" "x", .call none "init" ["p"]] = [.initializedArgument "p"] := by
  decide

/-- `int* s = alloc(); auto v = *s;`: the result refers to uninitialized
objects, the read is rejected, and it is undefined. -/
theorem ref_to_uninit_result :
    check okModel ok [.call (some "s") "alloc" [], .read "v" "s"] = [.readUninit "s"] ∧
    hazard okModel [.call (some "s") "alloc" [], .read "v" "s"] = true := by
  decide

/-- `int x [[uninit]]; destroy_fn(&x)` with a plain parameter: an
uninitialized argument is rejected ([profiles.init.ref]/4). -/
theorem plain_uninit_argument :
    check okModel { ok with uninit := ["x"] } [.var "x" int, .addr "p" "x", .call none "init2" ["p"]] =
      [.uninitArgument "p"] := by
  decide

/-! ## Across the call: what locality loses -/

/-- `C c{1}; destroy(&c); std::destroy_at(&c);`: `destroy`'s parameter is
plain, so the callee may destroy what it refers to and the caller is
told nothing. Accepted; the second destructor call is undefined
([class.dtor]/18). G2 across a call. -/
def calleeDestroysThenDestroy : Trace :=
  [.var "c" cC (.braces [1]), .addr "p" "c", .call none "destroy" ["p"], .destroy "p"]

theorem callee_destroys_then_destroy :
    accepts okModel ok calleeDestroysThenDestroy = true ∧
    run okModel calleeDestroysThenDestroy = .undefined .destructorOutsideLifetime := by
  decide

/-- `C c{1}; destroy(&c); auto v = c.i;`: accepted, undefined
([basic.life]/8). G1 across a call. -/
def calleeDestroysThenRead : Trace :=
  [.var "c" cC (.braces [1]), .addr "p" "c", .call none "destroy" ["p"], .member "pi" "p" 0, .read "v" "pi"]

theorem callee_destroys_then_read :
    accepts okModel ok calleeDestroysThenRead = true ∧ run okModel calleeDestroysThenRead = .undefined .outsideLifetime := by
  decide

/-- `const X* p = new const X{3}; reset(p); auto v = p->n;`: the callee
destroys and recreates behind a plain parameter, which its own body
check allows; the caller's pointer refers to the dead const object
([basic.life]/9). The [ptr.launder]/6 example, split across a call. -/
def calleeResets : Trace :=
  [.newObject "p" (.const cX) (.braces [3]), .call none "reset" ["p"], .member "pn" "p" 0, .read "v" "pn"]

theorem callee_resets :
    accepts okModel ok calleeResets = true ∧ run okModel calleeResets = .undefined .outsideLifetime := by
  decide

/-- `unsigned char buf [[uninit]] [4]; read_fn(buf); auto v =
*reinterpret_cast<int*>(buf);`: `[[now_init]]` asserts the body
initialized what nothing initialized. Accepted; the read is of erroneous
bytes. The declared hole, as a theorem. -/
def nowInitHole : Trace :=
  [.var "buf" uchar .default false 4, .addr "b" "buf", .call none "read_fn" ["b"], .cast "q" int "b", .read "v" "q"]

theorem now_init_hole :
    accepts okModel { ok with uninit := ["buf"] } nowInitHole = true ∧ hazard okModel nowInitHole = true := by
  decide

/-- `int* r = local(); auto v = *r;`: a pointer to the callee's automatic
object comes back invalid ([basic.compound]/6); the profile's return
rule is satisfied, since `x` was initialized. The invalidation profile's. -/
def danglingReturn : Trace := [.call (some "r") "local" [], .read "v" "r"]

theorem dangling_return :
    accepts okModel ok danglingReturn = true ∧ run okModel danglingReturn = .undefined .invalidPointer := by
  decide

/-- The table across calls. -/
def acceptedHazards : List Trace := [calleeDestroysThenDestroy, calleeDestroysThenRead, calleeResets, danglingReturn]

theorem accepted_hazards : acceptedHazards.all (fun t => accepts okModel ok t && hazard okModel t) = true := by decide

end Overload.Object.Functions
