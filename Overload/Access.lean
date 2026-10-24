-- Overload/Access.lean                                               -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Mandates
import Overload.Special

/-!
# Access to a base class

A derivation base that keeps its implementation as a protected base, as
`derive_functor<Impl>` does in beman.transpose, raises the question what a
non-public base does at a call.

It does not hide the base from overload resolution. Implicit conversion
sequences ignore the accessibility of the argument
([over.best.ics.general]/2), so a derived-to-base conversion to a
protected base is ranked like any other, and deduction from a derived
class sees it. Access is checked when the selected function's
conversions are formed: a conversion to an inaccessible base makes the
program ill-formed ([conv.ptr]/3, [dcl.init.ref]/4). A protected base
therefore turns a selection into a hard error at a call outside the
class, and never into a candidate that is not viable
(`protected_base_selected_ill_formed`).

The fragment has calls only outside every class, with no friends, so a
base is accessible exactly when every step of derivation to it is
public.
-/

namespace Overload

namespace Program

/-- The public direct bases a program declares for a class. -/
def publicBases (p : Program) : Ty → List Ty
  | .named n =>
    (p.findSome? fun
      | .class m bs _ _ => if m = n then some bs else none
      | _ => none).getD []
  | _ => []

/-- `b` is a base of `d` by public derivation at every step, within
`fuel` steps. -/
def derivesPubliclyWithin (p : Program) : Nat → Ty → Ty → Bool
  | 0, _, _ => false
  | fuel + 1, d, b => (p.publicBases d).any fun m => m == b || p.derivesPubliclyWithin fuel m b

/-- A base class is accessible from outside every class when each step of
derivation to it is public. -/
@[std rule "class.access.base#4"]
def accessibleBase (p : Program) (d b : Ty) : Bool := p.derivesPubliclyWithin p.length d b

/-- The conversion an argument needs for a parameter is well-formed as far
as access goes: no conversion, the identity, or a derived-to-base
conversion to an accessible base. -/
@[std rule "conv.ptr#3.sentence-2"]
def accessibleConversion (p : Program) (a : CallArg) (t : Ty) : Bool :=
  let std (s : StdConv) := s.rank == .exactMatch || p.accessibleBase s.source s.target
  match p.ics .copy a t with
  | some (.standard s) => std s
  | some (.userDefined f _ s) => std f && std s
  | _ => true

/-- Does the argument's conversion to the parameter use the ambiguous
conversion sequence? A function selected with one is ill-formed. -/
@[std rule "over.best.ics.general#12"]
def ambiguousConversion (p : Program) (a : CallArg) (t : Ty) : Bool :=
  p.ics .copy a t == some .ambiguous

/-- A call, as a program evaluates it in an environment, normally the one
the program defines (`Env.ofProgram`) or a layer above it: overload
resolution, which ignores access and ranks an ambiguous conversion
sequence as a user-defined one; then, on the selected function, an
argument whose conversion is ambiguous makes the call ill-formed; then
the copy-initialization of each by-value class parameter from an
argument of its class, which is ill-formed when the constructor selected
is deleted; then the access check on its conversions, after ambiguity
resolution, an inaccessible base making the call ill-formed; then the
selected specialization's Mandates. The candidates' associated
constraints are the normal forms of their constraint-expressions
(`Program.normalizeDecl`), so a concept-id is expanded before
satisfaction and subsumption see it. -/
@[std rule "dcl.init.ref#4.sentence-3" "class.conv.general#2"]
def call (p : Program) (env : Env) (decls : List Decl) (args : List CallArg)
    (explicit : List Ty := []) : Resolution Candidate :=
  let decls := decls.map p.normalizeDecl
  match resolve .text env p.ranking decls args explicit with
  | .selected c =>
    if (args.zip c.params).any fun (a, t) => p.ambiguousConversion a t then
      .illFormed "the conversion of an argument is ambiguous"
    else if !(args.zip c.params).all fun (a, t) => p.copyInitUsable a t then
      .illFormed "the copy-initialization of a parameter uses a deleted constructor"
    else if (args.zip c.params).all fun (a, t) => p.accessibleConversion a t then
      invoke .text env p.ranking decls args explicit
    else .illFormed "conversion to an inaccessible base class"
  | _ => invoke .text env p.ranking decls args explicit

end Program

/-- When the selected function's conversions are unambiguous and
accessible, the call is the evaluated call of `invoke`; the two checks
change nothing else. -/
theorem call_eq_invoke (p : Program) (env : Env) (decls : List Decl) (args : List CallArg)
    (explicit : List Ty)
    (hamb : ∀ c, resolve .text env p.ranking (decls.map p.normalizeDecl) args explicit = .selected c →
      ∀ x ∈ args.zip c.params, p.ambiguousConversion x.1 x.2 = false)
    (husable : ∀ c, resolve .text env p.ranking (decls.map p.normalizeDecl) args explicit = .selected c →
      ∀ x ∈ args.zip c.params, p.copyInitUsable x.1 x.2 = true)
    (h : ∀ c, resolve .text env p.ranking (decls.map p.normalizeDecl) args explicit = .selected c →
      ∀ x ∈ args.zip c.params, p.accessibleConversion x.1 x.2 = true) :
    p.call env decls args explicit =
      invoke .text env p.ranking (decls.map p.normalizeDecl) args explicit := by
  unfold Program.call
  simp only
  split
  · rename_i c hc
    simp only [List.any_eq_false.mpr fun x hx => by simpa using hamb c hc x hx,
      List.all_eq_true.mpr fun x hx => husable c hc x hx,
      List.all_eq_true.mpr fun x hx => h c hc x hx, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
  · rfl

/-! ## A protected base -/

/-- An implementation, a derivation base that has it as a protected base,
and a class derived publicly from that; and a function that names the
implementation. -/
def protectedProgram : Program :=
  [ .class "impl", .class "derive_impl" [] [.named "impl"], .class "map" [.named "derive_impl"]
  , .function "use" [.lref (.const (.named "impl"))] ]

/-- Overload resolution selects the function that names the
implementation, through the protected base, and the call is ill-formed:
not a candidate that is not viable, so no other overload is tried. -/
theorem protected_base_selected_ill_formed :
    (resolve .text (Env.ofProgram protectedProgram) protectedProgram.ranking
        (protectedProgram.candidates "use") [{ ty := .named "map", lvalue := true }]).map (·.index) =
      .selected 0 ∧
      ∃ e, protectedProgram.call (Env.ofProgram protectedProgram) (protectedProgram.candidates "use")
        [{ ty := .named "map", lvalue := true }] = .illFormed e :=
  ⟨rfl, ⟨_, rfl⟩⟩

/-- The same with a template that names the implementation's class
template: deduction from a derived class goes through the protected
base, and the selected call is ill-formed. -/
def protectedTemplateProgram : Program :=
  [ .classTemplate "impl_of" [{ kind := .type }], .class "int_impl_base" [] [.spec' "impl_of" [.named "int"]]
  , .class "int_map" [.named "int_impl_base"]
  , .functionTemplate { name := "use", head := [{ kind := .type }]
                        params := [.lref (.const (.spec' "impl_of" [.param 0]))] } ]

theorem protected_base_deduced_ill_formed :
    (resolve .text (Env.ofProgram protectedTemplateProgram) protectedTemplateProgram.ranking
        (protectedTemplateProgram.candidates "use") [{ ty := .named "int_map", lvalue := true }]).map
        (·.index) = .selected 0 ∧
      ∃ e, protectedTemplateProgram.call (Env.ofProgram protectedTemplateProgram) (protectedTemplateProgram.candidates "use")
        [{ ty := .named "int_map", lvalue := true }] = .illFormed e :=
  ⟨rfl, ⟨_, rfl⟩⟩

/-! ## The draft's narrowing example -/

/-- `template <int> int f(int); template <signed char> int f(int);`, the
example of [temp.deduct.general]/12. -/
def deductGeneral12Program : Program :=
  [ .functionTemplate { name := "f", head := [{ kind := .const (.named "int") }]
                        params := [.named "int"], ret := .named "int" }
  , .functionTemplate { name := "f", head := [{ kind := .const (.named "signed char") }]
                        params := [.named "int"], ret := .named "int" } ]

/-- `f<1000>(0)` is OK: a `signed char` cannot represent 1000, so the
conversion of the template argument of type `int` would narrow,
substitution fails for the second template, and the first is selected.
`f<1>(0)` is ambiguous: 1 is not narrowing, both are viable, and with
the same function parameter list neither is more specialized. -/
@[std example "temp.deduct.general#12"]
theorem temp_deduct_general_12_example :
    (deductGeneral12Program.call (Env.ofProgram deductGeneral12Program)
        (deductGeneral12Program.candidates "f") [{ ty := .named "int" }] [.value (.int 1000)]).map
        (·.index) = .selected 0 ∧
      (deductGeneral12Program.call (Env.ofProgram deductGeneral12Program)
        (deductGeneral12Program.candidates "f") [{ ty := .named "int" }] [.value (.int 1)]).map
        (·.index) = .ambiguous [0, 1] := by
  refine ⟨by decide, by decide⟩

end Overload
