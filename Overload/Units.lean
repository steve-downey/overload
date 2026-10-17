-- Overload/Units.lean                                                -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Sfinae

/-!
# Translation units, and what cannot be said about them

Phase 8. A program is a list of translation units, each resolved on its
own as before. The model gives no meaning to a program in which one
entity has two contrary definitions. It reports that the program is
ill-formed with no diagnostic required, names the rule and the use, and
says nothing more (`decisions.md#single-tu`).

The verdicts are about instance lookup. A use of a lookup, `tc<a>`,
selects among the partial specializations it can reach. The selection
must be the one it would make with every partial specialization of the
program reachable:

* one declared later in the same unit gives the specialization a second
  point of instantiation, at the end of the unit, with a different
  meaning ([temp.point]/7);
* one declared only in another unit is not reachable from a use that
  would make use of it ([temp.spec.partial.general]/1).

For one unit, the old standing assumption is exactly what rules both out
(`verdicts_single`).

divergence-separation compares what two units resolve when their lookups
differ. The plan expected separation wherever the instance is a template
argument. The canonical operation object has the instance as a template
argument, but as a reference to the lookup variable, which is one entity
in every unit: both units name one specialization with two meanings
(`operation_object_not_separated`). Pinning and the by-value policy name
the instance itself, and separate.
-/

namespace Overload

open PartialOrdering

/-- A program of several translation units. -/
abbrev Units := List Program

/-- The instances of `tc` that a list of declarations makes reachable,
each partial specialization once. -/
def reachable (p : Program) (tc : String) : List (Head × Ty) := (p.instancesOf tc).eraseDups

/-- The partial specializations of `tc` that the whole program declares. -/
def Units.instancesOf (us : Units) (tc : String) : List (Head × Ty) :=
  (us.flatMap fun p => p.instancesOf tc).eraseDups

/-- What a use selects, as the partial specialization itself rather than
its position, so that units can be compared. -/
def selection (insts : List (Head × Ty)) (tc : String) (a : Ty) : Resolution (Head × Ty) :=
  (select tc insts a).map fun i => insts.getD i default

/-- Ill-formed, no diagnostic required: the fourth outcome, a verdict about
the program at a use of a lookup. -/
@[specification]
inductive IllFormedNdr where
  /-- A partial specialization declared later in the use's unit would be
  selected at the unit's end, a second point of instantiation that gives
  the specialization a different meaning. -/
  | laterInUnit (unit pos : Nat) (tc : String) (arg : Ty)
  /-- A partial specialization of another unit would be selected, and it
  is not reachable from the use. -/
  | notReachable (unit pos : Nat) (tc : String) (arg : Ty)
  deriving Repr, DecidableEq

attribute [std rule "temp.point#7"] IllFormedNdr.laterInUnit
attribute [std rule "temp.spec.partial.general#1.sentence-3"] IllFormedNdr.notReachable

/-- The verdict at one use, the `pos`th declaration of unit `u`. -/
def useVerdict (us : Units) (u pos : Nat) (p : Program) (tc : String) (a : Ty) : Option IllFormedNdr :=
  let here := selection (reachable (p.take pos) tc) tc a
  if here != selection (reachable p tc) tc a then some (.laterInUnit u pos tc a)
  else if here != selection (us.instancesOf tc) tc a then some (.notReachable u pos tc a)
  else none

/-- Every verdict about the program. An empty list says nothing about
the program's meaning beyond these rules; a non-empty one says the
program has none. -/
def Units.verdicts (us : Units) : List IllFormedNdr :=
  us.zipIdx.flatMap fun (p, u) =>
    p.zipIdx.filterMap fun (d, pos) =>
      match d with
      | .use tc a => useVerdict us u pos p tc a
      | _ => none

/-! ## One unit -/

theorem instancesOf_take_drop (p : Program) (k : Nat) (tc : String)
    (h : (p.drop k).any (Program.isInstanceOf tc) = false) :
    Program.instancesOf (p.take k) tc = p.instancesOf tc := by
  have e := Program.instancesOf_append (p.take k) (p.drop k) tc
  rw [List.take_append_drop] at e
  have : Program.instancesOf (p.drop k) tc = [] := by
    unfold Program.instancesOf
    rw [List.filterMap_eq_nil_iff]
    intro d hd
    have := List.any_eq_false.mp h d hd
    cases d with
    | «instance» c hh pat =>
      simp only [Program.isInstanceOf, beq_iff_eq] at this
      simp [this]
    | _ => rfl
  rw [e, this, List.append_nil]

/-- For one unit, the standing assumption of the single translation unit
is what keeps every use free of a verdict: no instance is declared after
a use of its lookup. -/
theorem verdicts_single (p : Program) (h : SingleTranslationUnit p) : Units.verdicts [p] = [] := by
  unfold SingleTranslationUnit Program.declaredBeforeUse at h
  rw [List.all_eq_true] at h
  simp only [Units.verdicts, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.filterMap_eq_nil_iff]
  intro x hx
  obtain ⟨d, pos⟩ := x
  cases d with
  | use tc a =>
    have hd := h (.use tc a, pos) hx
    simp only [Bool.not_eq_true'] at hd
    have ht := instancesOf_take_drop p pos tc hd
    have hprog : Units.instancesOf [p] tc = reachable p tc := by
      simp [Units.instancesOf, reachable]
    simp only [useVerdict, reachable, ht, hprog, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  | _ => rfl

/-! ## Two units -/

private def T : Ty := .param 0
private def box (t : Ty) : Ty := .spec' "box" [t]
private def int : Ty := .named "int"

/-- A unit that declares an instance for `box<T>` and uses the lookup at
`box<int>`. -/
def unitWithInstance : Program :=
  [ .classTemplate "box" [{ kind := .type }], .lookup "functor"
  , .instance "functor" [{ kind := .type }] (box T), .use "functor" (box int) ]

/-- A unit that uses the lookup at `box<int>` without the instance. -/
def unitWithoutInstance : Program :=
  [ .classTemplate "box" [{ kind := .type }], .lookup "functor", .use "functor" (box int) ]

/-- A unit that declares the instance after its use. -/
def unitLateInstance : Program :=
  [ .classTemplate "box" [{ kind := .type }], .lookup "functor", .use "functor" (box int)
  , .instance "functor" [{ kind := .type }] (box T) ]

/-- Each unit alone is a well-formed program; together they are
ill-formed with no diagnostic required, at the use of the unit without
the instance. -/
theorem missing_instance_verdict :
    Units.verdicts [unitWithoutInstance] = [] ∧ Units.verdicts [unitWithInstance] = [] ∧
      Units.verdicts [unitWithInstance, unitWithoutInstance] = [.notReachable 1 2 "functor" (box int)] := by
  refine ⟨rfl, rfl, rfl⟩

/-- An instance declared after a use gives the lookup a second point of
instantiation with a different meaning. -/
theorem late_instance_verdict :
    Units.verdicts [unitLateInstance] = [.laterInUnit 0 2 "functor" (box int)] := rfl

/-! ## divergence-separation -/

section separation

variable (pA pB : Program) (tc : String) (f x : CallArg)

/-- The canonical operation object does not separate. In two units whose
lookups at the key both select an instance, whichever it is, deduction
produces one specialization, which names the lookup variable. The units
then give that one function two meanings, which the one-definition rule
forbids with no diagnostic required ([basic.def.odr]/16: corresponding
names denote the same entity after matching of partial specialization).
-/
theorem operation_object_not_separated (hf : f.ty.isType = true) (hx : x.ty.isType = true)
    (hfF : f.ty.formed = true) (hxF : x.ty.formed = true)
    (hfr : f.ty.isRef = false) (hxr : x.ty.isRef = false) (hxd : x.ty.dependent = false)
    (hlA : pA.any (fun | .lookup c => c = tc | _ => false) = true)
    (hhA : pA.any (fun | .lookupHard c => c = tc | _ => false) = false)
    (hlB : pB.any (fun | .lookup c => c = tc | _ => false) = true)
    (hhB : pB.any (fun | .lookupHard c => c = tc | _ => false) = false)
    (i j : Nat) (hA : pA.selectInstance tc x.ty.stripConst = .selected i)
    (hB : pB.selectInstance tc x.ty.stripConst = .selected j) :
    deduceTemplate (Env.ofProgram pA) (fmapObject tc) [] [f, x] =
      deduceTemplate (Env.ofProgram pB) (fmapObject tc) [] [f, x] := by
  rw [fmapObject_deduce pA tc f x hf hx hfF hxF hfr hxr hxd hlA hhA,
    fmapObject_deduce pB tc f x hf hx hfF hxF hfr hxr hxd hlB hhB, hA, hB]
  rfl

theorem parameterListStep_ok (env : Env) (h : Head) (σ σ' : Bindings)
    (e : parameterListStep env h σ = .ok σ') : σ' = σ := by
  simp only [parameterListStep, Subst.bind_eq] at e
  revert e
  generalize formAll env _ = r
  intro e
  cases r with
  | ok _ => simp only [Subst.bind_ok, Subst.pure_eq, Subst.ok.injEq] at e; exact e.symm
  | soft _ => cases e
  | hard _ => cases e

theorem constraintStep_ok (env : Env) (c : Option Constraint) (σ σ' : Bindings)
    (e : constraintStep env c σ = .ok σ') : σ' = σ := by
  cases c with
  | none => simp only [constraintStep, Subst.ok.injEq] at e; exact e.symm
  | some c =>
    simp only [constraintStep, Subst.bind_eq] at e
    cases hs : Constraint.satisfied env.atomic σ c with
    | ok b =>
      rw [hs] at e
      cases b
      · cases e
      · simp only [Subst.bind_ok, ↓reduceIte, Subst.pure_eq, Subst.ok.injEq] at e; exact e.symm
    | soft _ => rw [hs] at e; cases e
    | hard _ => rw [hs] at e; cases e

theorem functionTypeStep_args (env : Env) (ft : FunctionTemplate) (σ : Bindings) (s : Specialization)
    (e : functionTypeStep env ft σ = .ok s) : s.args = σ := by
  simp only [functionTypeStep, Subst.bind_eq] at e
  cases hp : formAll env (ft.params.map (Ty.subst σ)) with
  | ok _ =>
    rw [hp] at e
    simp only [Subst.bind_ok] at e
    cases hr : form env (ft.ret.subst σ) with
    | ok _ => rw [hr] at e; simp only [Subst.bind_ok, Subst.pure_eq, Subst.ok.injEq] at e; rw [← e]
    | soft _ => rw [hr] at e; cases e
    | hard _ => rw [hr] at e; cases e
  | soft _ => rw [hp] at e; cases e
  | hard _ => rw [hp] at e; cases e

/-- The by-value policy type the omitted route defaults to: the type of
the value the unit's lookup gives. -/
def policyOf (v : Ty) : Ty := if v.dependent then .typeOf v else v.typeOfValue

/-- With the policy omitted, a deduced specialization of the by-value
route carries as its policy the type of the value the unit's lookup
gives. -/
theorem byValue_policy (p : Program) (hx : x.ty.isType = true) (hf : f.ty.isType = true)
    (hxF : x.ty.formed = true) (hxr : x.ty.isRef = false) (hxd : x.ty.dependent = false)
    (s : Specialization)
    (h : deduceTemplate (Env.ofProgram p) (byValueObject tc) [] [f, x] = .ok s) :
    ∃ v, (Env.ofProgram p).instantiate tc x.ty.stripConst = .ok v ∧ s.args.lookup 2 = some (policyOf v) := by
  simp only [deduceTemplate] at h
  rw [byValue_call_omitted _ tc f x hf hx] at h
  simp only [Subst.bind_eq, Subst.bind_ok] at h
  rw [byValue_defaults tc f x _ hx hxF hxr hxd] at h
  cases hv : (Env.ofProgram p).instantiate tc x.ty.stripConst with
  | ok v =>
    rw [hv] at h
    refine ⟨v, rfl, ?_⟩
    simp only [Subst.bind_ok] at h
    generalize hσ : ((2, if v.dependent then .typeOf v else v.typeOfValue) :: [(1, forwarded x), (0, forwarded f)] : Bindings) = σ at h
    cases h₁ : parameterListStep (Env.ofProgram p) (byValueObject tc).head σ with
    | ok σ₁ =>
      rw [h₁] at h
      have e₁ := parameterListStep_ok _ _ _ _ h₁
      simp only [Subst.bind_ok] at h
      cases h₂ : constraintStep (Env.ofProgram p) (byValueObject tc).constraint σ₁ with
      | ok σ₂ =>
        rw [h₂] at h
        have e₂ := constraintStep_ok _ _ _ _ h₂
        simp only [Subst.bind_ok] at h
        cases h₃ : nonDependentStep (Env.ofProgram p) (byValueObject tc).params [f, x] σ₂ with
        | ok σ₃ =>
          rw [h₃] at h
          have e₃ := nonDependentStep_ok _ _ _ _ _ h₃
          simp only [Subst.bind_ok] at h
          rw [functionTypeStep_args _ _ _ _ h, e₃, e₂, e₁, ← hσ]
          simp [Bindings.lookup, policyOf]
        | soft _ => rw [h₃] at h; cases h
        | hard _ => rw [h₃] at h; cases h
      | soft _ => rw [h₂] at h; cases h
      | hard _ => rw [h₂] at h; cases h
    | soft _ => rw [h₁] at h; cases h
    | hard _ => rw [h₁] at h; cases h
  | soft _ => rw [hv] at h; cases h
  | hard _ => rw [hv] at h; cases h

/-- The by-value route separates, as far as instance types do. In two
units whose lookups at the key give values of different types, the
deduced specializations differ. -/
theorem byValue_separated (hx : x.ty.isType = true) (hf : f.ty.isType = true)
    (hxF : x.ty.formed = true) (hxr : x.ty.isRef = false) (hxd : x.ty.dependent = false)
    (sA sB : Specialization)
    (hA : deduceTemplate (Env.ofProgram pA) (byValueObject tc) [] [f, x] = .ok sA)
    (hB : deduceTemplate (Env.ofProgram pB) (byValueObject tc) [] [f, x] = .ok sB)
    (hne : ∀ vA vB, (Env.ofProgram pA).instantiate tc x.ty.stripConst = .ok vA →
      (Env.ofProgram pB).instantiate tc x.ty.stripConst = .ok vB → policyOf vA ≠ policyOf vB) :
    sA ≠ sB := by
  obtain ⟨vA, hvA, hpA⟩ := byValue_policy tc f x pA hx hf hxF hxr hxd sA hA
  obtain ⟨vB, hvB, hpB⟩ := byValue_policy tc f x pB hx hf hxF hxr hxd sB hB
  intro e
  subst e
  rw [hpA] at hpB
  exact hne vA vB hvA hvB (Option.some.inj hpB)

end separation

end Overload
