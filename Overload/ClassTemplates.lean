-- Overload/ClassTemplates.lean                                       -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Members
import Overload.Environment

/-!
# Class templates and their members

A class template's members are declarations for its current
instantiation, `X<T0, …>` (`currentInstantiation`), and its member
functions are declarations in its scope, which is a class scope. A
specialization has the template's member declarations with its
arguments substituted (`Decl.instantiate`), which is the implicit
instantiation of their declarations that looking into the
specialization requires ([temp.inst]/2, /3); the argument list is
determined by the type ([temp.mem.func]/2, `Program.classKey?`). A
member template's own parameters follow the class's in the numbering
([temp.mem]/1), and the same substitution renumbers them from zero.

* `instantiate_ground`: a class's member is the declaration itself;
  there is nothing to substitute.
* `member_template_arguments_example`: for a member template of a class
  template specialization, deduction binds the member's own parameters
  only, and gives the function type that deduction for the member with
  the class's arguments as leading explicit arguments gives
  ([temp.mem.func]/2). Shown by computation on `holder<int>`; the
  general statement is owed (`docs/plan.md`, phase 15).
-/

namespace Overload

/-- A class's member is its declaration: with no template arguments
there is nothing to substitute. -/
theorem instantiate_ground (d : Decl) : Decl.instantiate [] d = d := by
  simp [Decl.instantiate]

/-- The class template's key is its own name with no arguments. -/
theorem classKey?_named (p : Program) (n : String) : p.classKey? (.named n) = some (.named n, []) := rfl

/-- `template <class T> struct holder { T m; template <class U> void f(T, U) const; };`,
with the member template's own parameter numbered after the class's. -/
def holderProgram : Program :=
  [ .classTemplate "holder" [{ kind := .type }]
  , .member (currentInstantiation "holder" [{ kind := .type }]) { name := "m", ty := .param 0 }
  , .functionTemplate holderMember ]
where
  /-- The member template as declared in the class template: `T` is
  `.param 0`, the class's; `U` is `.param 1`, its own. -/
  holderMember : FunctionTemplate :=
    { name := "f", head := [{ kind := .type }], params := [.param 0, .param 1]
      scope := [.class "holder"] }

/-- The member template of `holder<int>`: `template <class U> void f(int, U)`. -/
theorem holder_int_member :
    Decl.instantiate [.named "int"] (.functionTemplate holderProgram.holderMember) =
      .functionTemplate { name := "f", head := [{ kind := .type }], params := [.named "int", .param 0]
                          scope := [.class "holder"] } := by
  decide

/-- The data member of `holder<int>` is `int m`. -/
theorem holder_int_data :
    holderProgram.membersOf (.spec' "holder" [.named "int"]) = [{ name := "m", ty := .named "int" }] := by
  decide

/-- The member template with the class's head prepended, as an out-of-line
definition writes it: `template <class T> template <class U> void
holder<T>::f(T, U)`. -/
def holderProgram.combined : FunctionTemplate :=
  { holderProgram.holderMember with head := [{ kind := .type }, { kind := .type }] }

/-- Deduction for the instantiated member of `holder<int>` at `(int, char)`
binds `U` alone and gives the function type `(int, char)`; deduction for
the combined template with `int` as the leading explicit argument gives
the same function type, with `T` bound as well. -/
@[std example "temp.mem.func#2"]
theorem member_template_arguments_example :
    let env := Env.ofProgram holderProgram
    let args : List CallArg := [{ ty := .named "int" }, { ty := .named "char" }]
    (deduceTemplate env { holderProgram.holderMember with params := [.named "int", .param 0] } [] args).map
        (fun s => (s.args, s.params)) =
      .ok ([(0, .named "char")], [.named "int", .named "char"]) ∧
    (deduceTemplate env holderProgram.combined [.named "int"] args).map (fun s => (s.args, s.params)) =
      .ok ([(1, .named "char"), (0, .named "int")], [.named "int", .named "char"]) := by
  constructor <;> rfl

end Overload
