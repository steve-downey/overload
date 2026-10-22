-- Overload/Identity.lean                                             -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Steps

/-!
# The identity of a specialization through its converted arguments

Two template-ids of one template are the same when the parameter values
determined by their constant template arguments are
template-argument-equivalent ([temp.type]/1), and the model's
equivalence is equality (`Val.equivalent_iff`): two explicit argument
lists name one specialization when the explicit step gives one bindings
list (`sameSpecialization`). Two consequences, for the constant
parameters a typeclass encoding can give its instances:

* `slicing_identifies`: under a base-typed value parameter, a derived
  value and the base's own value determine the same specialization. A
  derived instance passed by value silently becomes its base, which is
  leak 4 of `decisions.md#instance-inheritance`.
* `reference_keeps_identity`: under a reference parameter the parameter
  denotes the argument's object ([temp.type]/2), so two objects, a
  derived instance and the base's, never name one specialization. The
  library's `const auto&` parameters are what closes the leak.

The type a placeholder deduces must be permitted for a constant template
parameter ([temp.arg.nontype]/1), that is structural ([temp.param]/12): a
class whose bases are all public and structural. `Program.structural` is
that check at the program level, where the class declarations are, and
`placeholderArgumentsPermitted` applies it to the class values among a
template-id's explicit arguments.
-/

namespace Overload

/-! ## One specialization -/

/-- Two explicit template argument lists name the same specialization of
a template with this head: the parameter values they determine, which
the explicit step records, are the same. -/
@[std rule "temp.type#1"]
def sameSpecialization (env : Env) (head : Head) (as bs : List Ty) : Prop :=
  explicitStep env head as = explicitStep env head bs

/-- A base-typed class value parameter: a value of a derived class, whose
base subobject of the parameter's class is `w`, and `w` itself name one
specialization. The derived value is sliced to the base's. -/
@[std theorem "temp.type#1"]
theorem slicing_identifies (env : Env) (b d : String) (vs ws : Val) (ps : Head) (rest : List Ty)
    (hp : (Ty.named b).hasPlaceholder = false) (hb : isInteger b = false) (hne : b ≠ d)
    (hs : env.subobject (.named b) (.obj d vs) = some (.obj b ws)) :
    sameSpecialization env ({ kind := .const (.named b) } :: ps)
      (.value (.obj d vs) :: rest) (.value (.obj b ws) :: rest) := by
  have hd : convertArg env.subobject [] (.const (.named b)) (.value (.obj d vs)) =
      .ok (.value (.obj b ws)) :=
    (convertArg_iff _ _ _ _ _).mp (.classBase (.named b) b d vs (.obj b ws) hp rfl rfl hb hne hs)
  have hb' : convertArg env.subobject [] (.const (.named b)) (.value (.obj b ws)) =
      .ok (.value (.obj b ws)) :=
    (convertArg_iff _ _ _ _ _).mp (.classSame (.named b) b ws hp rfl rfl hb)
  exact explicitStep_converted env _ ps _ _ rest rfl (hd.trans hb'.symm)

/-- A reference parameter: the parameter denotes the object the argument
designates, so two different objects never name one specialization,
whatever their classes. -/
@[std theorem "temp.type#2"]
theorem reference_keeps_identity (env : Env) (b : String) (r₁ r₂ : Ty) (ps : Head)
    (hp : (Ty.named b).hasPlaceholder = false) (hne : r₁ ≠ r₂) :
    ¬ sameSpecialization env ({ kind := .const (.lref (.const (.named b))) } :: ps) [.ref r₁] [.ref r₂] := by
  have hc : ∀ r, convertArg env.subobject [] (.const (.lref (.const (.named b)))) (.ref r) = .ok (.ref r) :=
    fun r => (convertArg_iff _ _ _ _ _).mp (.reference _ r (.const (.named b)) hp rfl rfl)
  intro h
  unfold sameSpecialization at h
  simp only [explicitStep, explicitStep.go, List.getElem?_cons_zero, kindMatches, Ty.isType, hc,
    Bool.not_false, ↓reduceIte, Subst.ok.injEq, List.cons.injEq, Prod.mk.injEq, Ty.ref.injEq,
    true_and, and_true] at h
  exact hne h

/-! ## Structural types -/

/-- `structuralWithin p fuel t`: is `t` a structural type, within `fuel`
steps of derivation? A scalar type, an lvalue reference type, or a
literal class type whose bases and members are all public and
structural; the fragment has no data members, and a protected base is a
non-public one. -/
def Program.structuralWithin (p : Program) : Nat → Ty → Bool
  | 0, _ => false
  | fuel + 1, t =>
    match t with
    | .named n =>
      if isInteger n then true
      else
        match p.findSome? (fun | .class m bs ps _ => if m = n then some (bs, ps) else none | _ => none) with
        | some (bs, ps) => ps.isEmpty && bs.all (p.structuralWithin fuel)
        | none => false
    | .lref _ => true
    | _ => false

/-- A structural type. -/
@[std rule "temp.param#12"]
def Program.structural (p : Program) (t : Ty) : Bool := p.structuralWithin (p.length + 1) t

/-- The type a placeholder parameter deduces from a class value shall be
permitted for a constant template parameter: for every class value among
the explicit arguments of a template-id whose parameter's declared type
contains a placeholder, the value's class is structural. -/
@[std rule "temp.arg.nontype#1.sentence-3"]
def Program.placeholderArgumentsPermitted (p : Program) (head : Head) (explicit : List Ty) : Bool :=
  (head.zip explicit).all fun (q, a) =>
    match q.kind, a with
    | .const t, .value (.obj c _) => !t.hasPlaceholder || p.structural (.named c)
    | _, _ => true

end Overload
