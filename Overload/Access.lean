-- Overload/Access.lean                                               -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Mandates

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
  match p.ics a t with
  | some s => s.rank == .exactMatch || p.accessibleBase s.source s.target
  | none => true

/-- A call, as a program evaluates it in an environment, normally the one
the program defines (`Env.ofProgram`) or a layer above it: overload
resolution, which ignores access; then the access check on the selected
function's conversions, an inaccessible base making the call ill-formed;
then the selected specialization's Mandates. -/
@[std rule "dcl.init.ref#4.sentence-3"]
def call (p : Program) (env : Env) (decls : List Decl) (args : List CallArg)
    (explicit : List Ty := []) : Resolution Candidate :=
  match resolve .text env p.ranking decls args explicit with
  | .selected c =>
    if (args.zip c.params).all fun (a, t) => p.accessibleConversion a t then
      invoke .text env p.ranking decls args explicit
    else .illFormed "conversion to an inaccessible base class"
  | _ => invoke .text env p.ranking decls args explicit

end Program

/-- When the selected function's conversions are accessible, the call is
the evaluated call of `invoke`; access changes nothing else. -/
theorem call_eq_invoke (p : Program) (env : Env) (decls : List Decl) (args : List CallArg)
    (explicit : List Ty)
    (h : ∀ c, resolve .text env p.ranking decls args explicit = .selected c →
      ∀ x ∈ args.zip c.params, p.accessibleConversion x.1 x.2 = true) :
    p.call env decls args explicit = invoke .text env p.ranking decls args explicit := by
  unfold Program.call
  split
  · rename_i c hc
    simp only [List.all_eq_true.mpr fun x hx => h c hc x hx, ↓reduceIte]
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

end Overload
