-- Overload/Virtual.lean                                              -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Ranking

/-!
# Virtual functions

Which member functions of a class are virtual, by [class.virtual]/1 and
/2: those first declared `virtual`, and those that override a virtual
function of a base, which is correspondence of the declarations. From
that, the polymorphic classes, the final overriders a class's objects
see, the abstract classes of [class.abstract]/2 and /4, and the virtual
destructor a class inherits, which has no sentence of its own in N5054:
a prospective destructor of a derived class corresponds to a base's and
so overrides it.

Correspondence itself is `Corresponds` in `Overload/Scope.lean`, above
this module in the layering; on two function declarations it is the
same name and the same parameter-type-list, which `sameSignature`
computes here, and `override_is_correspondence` there says so.

Everything is fuel-bounded through the program, as `derives` is: a base
is complete before the class that names it. The fuel's zero case keeps
the class's own declarations, so that a fact about a base within the
fuel of a derivation is a fact about the derived class within the same
fuel (`virtualDtorWithin_derives`).

Out of the fragment, by `decisions.md#virtual-fragment`: virtual base
classes and the unique final overrider across them, covariant return
types, `final` on a class, the definition requirement of
[class.virtual]/12, and the dynamic type.
-/

namespace Overload

/-- The virtuality a declaration carries: a function's, `.none` for
anything else. -/
def Decl.virt : Decl → Virt
  | .function _ _ _ v _ => v
  | _ => .none

/-- Is a function declaration potentially throwing, the predicate that is
its exception specification: its noexcept-specifier says so, or it has
none and the function, user-provided, is potentially throwing. Nothing
but a function declaration is asked. -/
@[std rule "except.spec#1" "except.spec#4"]
def Decl.throwing : Decl → Bool
  | .function _ _ _ _ ne => ne != some true
  | _ => true

namespace Program

/-- The member function declarations of a class: the functions whose
scope ends in the class's step. -/
def memberFunctions (p : Program) : Ty → List Decl
  | .named n => p.filter fun
      | .function _ _ s _ _ => s.getLast? == some (.class n)
      | _ => false
  | _ => []

/-- Two function declarations with the same name and the same
parameter-type-list: corresponding declarations, for the fragment's
member functions, which have no object parameters, ref-qualifiers or
trailing requires-clauses to compare. -/
@[std rule "class.virtual#2"]
def sameSignature : Decl → Decl → Bool
  | .function n ps _ _ _, .function m qs _ _ _ => n == m && ps == qs
  | _, _ => false

/-- The virtual member functions a class's objects have, within `fuel`
steps of derivation: the class's own member functions that are declared
virtual or that override a virtual function of a base, and the bases'
virtual functions no member of the class overrides. Each is a final
overrider at the class. With no virtual bases in the fragment, the
virtual functions of one signature in two bases are the final overriders
of two subobjects, which is well-formed. -/
@[std rule "class.virtual#1" "class.virtual#2"]
def virtualFunctionsWithin (p : Program) : Nat → Ty → List Decl
  | 0, c => (p.memberFunctions c).filter (·.virt.declared)
  | fuel + 1, c =>
    let own := p.memberFunctions c
    let inherited := (p.directBases c).flatMap (p.virtualFunctionsWithin fuel)
    own.filter (fun g => g.virt.declared || inherited.any (sameSignature · g)) ++
      inherited.filter fun f => !own.any (sameSignature f ·)

/-- The virtual member functions a class's objects have. -/
def virtualFunctions (p : Program) (c : Ty) : List Decl := p.virtualFunctionsWithin p.length c

/-- Does the member function declaration `g` of class `c` override a
virtual function of a base: does it correspond to one of the virtual
functions a direct base's objects have? A virtual function need not be
visible to be overridden: a base's declaration hidden by a member of
another signature is still among the base's virtual functions. -/
@[std rule "class.virtual#2" "class.virtual#3"]
def overrides (p : Program) (c : Ty) (g : Decl) : Bool :=
  (p.directBases c).any fun b => (p.virtualFunctions b).any (sameSignature · g)

/-- The final overrider at class `c` of the virtual function `f`, if the
class's objects have one of its signature. -/
@[std rule "class.virtual#2"]
def finalOverrider (p : Program) (c : Ty) (f : Decl) : Option Decl :=
  (p.virtualFunctions c).find? (sameSignature f ·)

/-- Has the class a user-declared destructor declared virtual, pure or
`final`? -/
@[std rule "class.dtor#11"]
def declaredVirtualDtor (p : Program) (c : Ty) : Bool :=
  (p.specialDecls c).any fun s => s.kind == .dtor && s.virt.declared

/-- Has the class a user-declared destructor with a pure-specifier? -/
@[std rule "class.dtor#11" "class.abstract#2"]
def pureDtor (p : Program) (c : Ty) : Bool :=
  (p.specialDecls c).any fun s => s.kind == .dtor && s.virt == .pure

/-- Has the class a virtual destructor, within `fuel` steps of derivation:
its own prospective destructor declared virtual, or a base's virtual
destructor, which the class's destructor, user-declared or implicit,
overrides, since prospective destructors correspond. -/
@[std rule "class.dtor#11" "class.virtual#2"]
def virtualDtorWithin (p : Program) : Nat → Ty → Bool
  | 0, c => p.declaredVirtualDtor c
  | fuel + 1, c => p.declaredVirtualDtor c || (p.directBases c).any (p.virtualDtorWithin fuel)

/-- Has the class a virtual destructor? -/
def virtualDtor (p : Program) (c : Ty) : Bool := p.virtualDtorWithin p.length c

/-- A polymorphic class: one with a virtual member function, its
destructor included. -/
@[std rule "class.virtual#1"]
def polymorphic (p : Program) (c : Ty) : Bool :=
  !(p.virtualFunctions c).isEmpty || p.virtualDtor c

/-- An abstract class: one with a pure virtual function whose final
overrider is pure virtual, which is a pure function among the virtual
functions its objects have, or a destructor declared pure. A derived
class's destructor overrides a pure one and is not itself pure unless
declared so. -/
@[std rule "class.abstract#2" "class.abstract#4"]
def abstract (p : Program) (c : Ty) : Bool :=
  (p.virtualFunctions c).any (·.virt == .pure) || p.pureDtor c

/-- The virt-specifiers of the program are well-formed: no member
function overrides a `final` one; a member function declared `override`
overrides something; no member function with a potentially-throwing
exception specification overrides a non-throwing virtual function; no
class derives from one whose destructor is `final`, since its own
destructor, declared or implicit, would override it; and a destructor
declared `override` has a virtual one to override. A program-level
check, like `scopesWellFormed`. The destructor's case of the exception
rule is decided above this module, with the implicit specifications, and
is not checked here. -/
@[std rule "class.virtual#4" "class.virtual#5" "except.spec#5"]
def virtualsWellFormed (p : Program) : Bool :=
  let finalDtor (c : Ty) : Bool := (p.specialDecls c).any fun s => s.kind == .dtor && s.virt == .final
  p.all fun
    | g@(.function _ _ s v _) =>
      match s.getLast? with
      | some (.class n) =>
        let overridden :=
          ((p.directBases (.named n)).flatMap (p.virtualFunctions ·)).filter (sameSignature · g)
        !overridden.any (·.virt == .final) && (v != .override || !overridden.isEmpty) &&
        !(g.throwing && overridden.any (!·.throwing))
      | _ => true
    | .class n _ _ _ => !(p.directBases (.named n)).any finalDtor
    | .special c s =>
      s.kind != .dtor || s.virt != .override || (p.directBases c).any (p.virtualDtor ·)
    | _ => true

end Program

/-! ## Theorems -/

/-- A declared virtual destructor is one within any fuel. -/
theorem virtualDtorWithin_of_declared (p : Program) (n : Nat) (c : Ty)
    (h : p.declaredVirtualDtor c = true) : p.virtualDtorWithin n c = true := by
  cases n <;> simp [Program.virtualDtorWithin, h]

/-- A class derived within `fuel` from one with a declared virtual
destructor has a virtual destructor within the same fuel. -/
theorem virtualDtorWithin_derives (p : Program) : ∀ (fuel : Nat) (d b : Ty),
    p.derivesWithin fuel d b = true → p.declaredVirtualDtor b = true →
      p.virtualDtorWithin fuel d = true := by
  intro fuel
  induction fuel with
  | zero => intro d b h; simp [Program.derivesWithin] at h
  | succ n ih =>
    intro d b h hb
    simp only [Program.derivesWithin, List.any_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨m, hm, h⟩ := h
    simp only [Program.virtualDtorWithin, Bool.or_eq_true, List.any_eq_true]
    rcases h with rfl | hmb
    · exact Or.inr ⟨m, hm, virtualDtorWithin_of_declared p n m hb⟩
    · exact Or.inr ⟨m, hm, ih m b hmb hb⟩

/-- A class derived from one with a declared virtual destructor has a
virtual destructor, declared or implicit: its prospective destructor
corresponds to the base's and overrides it. N5054 has no sentence
saying so; it is [class.virtual]/2 applied to [class.dtor]/11. -/
@[std theorem "class.virtual#2" "class.dtor#11"]
theorem virtual_destructor_inherited (p : Program) (d b : Ty) (hd : p.derives d b = true)
    (hb : p.declaredVirtualDtor b = true) : p.virtualDtor d = true :=
  virtualDtorWithin_derives p p.length d b hd hb

/-- Every virtual function a class's objects have is a function
declaration. -/
theorem virtualFunctionsWithin_function (p : Program) : ∀ (n : Nat) (c : Ty) (f : Decl),
    f ∈ p.virtualFunctionsWithin n c → ∃ a ps s v ne, f = .function a ps s v ne := by
  have hmem : ∀ c f, f ∈ p.memberFunctions c → ∃ a ps s v ne, f = .function a ps s v ne := by
    intro c f hf
    cases c <;> simp only [Program.memberFunctions, List.mem_filter, List.not_mem_nil] at hf
    · obtain ⟨-, hf⟩ := hf
      cases f <;> simp at hf
      exact ⟨_, _, _, _, _, rfl⟩
    all_goals exact hf.elim
  intro n
  induction n with
  | zero =>
    intro c f hf
    simp only [Program.virtualFunctionsWithin, List.mem_filter] at hf
    exact hmem c f hf.1
  | succ n ih =>
    intro c f hf
    simp only [Program.virtualFunctionsWithin, List.mem_append, List.mem_filter, List.mem_flatMap] at hf
    rcases hf with ⟨hf, -⟩ | ⟨⟨b, -, hf⟩, -⟩
    · exact hmem c f hf
    · exact ih b f hf

/-- An abstract class is polymorphic: a pure virtual function is a
virtual function, and a pure destructor a virtual one. -/
@[std theorem "class.abstract#2" "class.virtual#1"]
theorem abstract_polymorphic (p : Program) (c : Ty) (h : p.abstract c = true) :
    p.polymorphic c = true := by
  simp only [Program.abstract, Bool.or_eq_true, List.any_eq_true] at h
  simp only [Program.polymorphic, Bool.or_eq_true, Bool.not_eq_true']
  rcases h with ⟨f, hf, -⟩ | h
  · exact Or.inl (List.isEmpty_eq_false_iff_exists_mem.mpr ⟨f, hf⟩)
  · refine Or.inr (virtualDtorWithin_of_declared p _ c ?_)
    simp only [Program.pureDtor, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨s, hs, hk, hv⟩ := h
    simp only [Program.declaredVirtualDtor, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
    exact ⟨s, hs, hk, by rw [hv]; rfl⟩

/-! ## The draft's example on overriding a non-throwing function -/

/-- `struct B { virtual void f() noexcept; virtual void g(); }; struct D : B
{ void f(); void g() noexcept; };`, the example of [except.spec]/5, and the
same with `D::f() noexcept`. -/
def overrideNoexceptProgram (fixed : Bool) : Program :=
  [ .class "B", .function "f" [] [.class "B"] .virtual (some true), .function "g" [] [.class "B"] .virtual
  , .class "D" [.named "B"], .function "f" [] [.class "D"] .none (if fixed then some true else none)
  , .function "g" [] [.class "D"] .none (some true) ]

/-- `D::f` is ill-formed: it overrides the non-throwing `B::f` with a
potentially-throwing exception specification; `D::g` may tighten `B::g`;
with `D::f` non-throwing the program is well-formed. -/
@[std example "except.spec#5"]
theorem override_keeps_noexcept :
    (overrideNoexceptProgram false).virtualsWellFormed = false ∧
    (overrideNoexceptProgram true).virtualsWellFormed = true := by
  decide

/-! ## The draft's note on visibility -/

/-- `struct B { virtual void f(); }; struct D : B { void f(int); };
struct D2 : D { void f(); };`, the note of [class.virtual]/3. -/
def hiddenVirtualProgram : Program :=
  [ .class "B", .function "f" [] [.class "B"] .virtual
  , .class "D" [.named "B"], .function "f" [.named "int"] [.class "D"]
  , .class "D2" [.named "D"], .function "f" [] [.class "D2"] ]

/-- `D::f(int)` hides `B::f()` and does not override it, so it is not
virtual; `D2::f()` overrides `B::f()` though `B::f()` is not visible in
`D2`; and all three classes are polymorphic. -/
@[std note "class.virtual#3"]
theorem hidden_virtual_example :
    hiddenVirtualProgram.overrides (.named "D") (.function "f" [.named "int"] [.class "D"]) = false ∧
    hiddenVirtualProgram.virtualFunctions (.named "D") = [.function "f" [] [.class "B"] .virtual] ∧
    hiddenVirtualProgram.overrides (.named "D2") (.function "f" [] [.class "D2"]) = true ∧
    hiddenVirtualProgram.virtualFunctions (.named "D2") = [.function "f" [] [.class "D2"]] ∧
    [Ty.named "B", .named "D", .named "D2"].all hiddenVirtualProgram.polymorphic = true := by
  decide

end Overload
