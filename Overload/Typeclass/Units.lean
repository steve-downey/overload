-- Overload/Typeclass/Units.lean                                      -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Units
import Overload.Typeclass.Routes

/-!
# The encoding across translation units

divergence-separation compares what two units resolve when their lookups
differ. The plan expected separation wherever the instance is a template
argument. The canonical operation object has the instance as a template
argument, but as a reference to the lookup variable, which is one entity
in every unit: both units name one specialization with two meanings
(`operation_object_not_separated`), ill-formed with no diagnostic required
([basic.def.odr]/16). Pinning names the instance object and separates. The
by-value policy names the instance's type, and separates as far as
instance types are distinct (`byValue_separated`).

Stability at the call surface is stated per unit (`call_stability_unit`):
an instance declared after the call leaves it unchanged, and one declared
before it moves the call as `call_stability` says, on the call's prefix.
The verdicts themselves are the Standard side's, in `Overload/Units.lean`.
-/

namespace Overload.Typeclass

open PartialOrdering

/-! ## divergence-separation -/

section separation

variable (pA pB : Program) (tc : String) (f x : CallArg)

/-- The canonical operation object does not separate. In two units whose
lookups at the key both select an instance, whichever it is, deduction
produces one specialization, which names the lookup variable. The units
then give that one function two meanings, which the one-definition rule
forbids with no diagnostic required: the verdict is
`IllFormedNdr.odrMismatch` at the lookup the specialization names
(`Units.odrVerdicts`, [basic.def.odr]/16), and `odr_verdict_implies_verdict`
says a verdict of phase 8 is already there. -/
theorem operation_object_not_separated (hf : f.ty.isType = true) (hx : x.ty.isType = true)
    (hfF : f.ty.formed = true) (hxF : x.ty.formed = true)
    (hfr : f.ty.isRef = false) (hxr : x.ty.isRef = false) (hxd : x.ty.dependent = false)
    (hlA : pA.any (fun | .lookup c => c = tc | _ => false) = true)
    (hhA : pA.any (fun | .lookupHard c => c = tc | _ => false) = false)
    (hlB : pB.any (fun | .lookup c => c = tc | _ => false) = true)
    (hhB : pB.any (fun | .lookupHard c => c = tc | _ => false) = false)
    (i j : Nat) (hA : pA.selectInstance tc x.ty.stripConst = .selected i)
    (hB : pB.selectInstance tc x.ty.stripConst = .selected j) :
    deduceTemplate (encodingEnv pA) (fmapObject tc) [] [f, x] =
      deduceTemplate (encodingEnv pB) (fmapObject tc) [] [f, x] := by
  rw [fmapObject_deduce pA tc f x hf hx hfF hxF hfr hxr hxd hlA hhA,
    fmapObject_deduce pB tc f x hf hx hfF hxF hfr hxr hxd hlB hhB, hA, hB]
  rfl



/-- The by-value policy type the omitted route defaults to: the type of
the value the unit's lookup gives. -/
def policyOf (v : Ty) : Ty := if v.dependent then .typeOf v else v.typeOfValue

/-- With the policy omitted, a deduced specialization of the by-value
route carries as its policy the type of the value the unit's lookup
gives. -/
theorem byValue_policy (p : Program) (hx : x.ty.isType = true) (hf : f.ty.isType = true)
    (hxF : x.ty.formed = true) (hxr : x.ty.isRef = false) (hxd : x.ty.dependent = false)
    (s : Specialization)
    (h : deduceTemplate (encodingEnv p) (byValueObject tc) [] [f, x] = .ok s) :
    ∃ v, (encodingEnv p).instantiate tc x.ty.stripConst = .ok v ∧ s.args.lookup 2 = some (policyOf v) := by
  simp only [deduceTemplate] at h
  rw [byValue_call_omitted _ tc f x hf hx] at h
  simp only [Subst.bind_eq, Subst.bind_ok] at h
  rw [byValue_defaults tc f x _ hx hxF hxr hxd] at h
  cases hv : (encodingEnv p).instantiate tc x.ty.stripConst with
  | ok v =>
    rw [hv] at h
    refine ⟨v, rfl, ?_⟩
    simp only [Subst.bind_ok] at h
    generalize hσ : ((2, if v.dependent then .typeOf v else v.typeOfValue) :: [(1, forwarded x), (0, forwarded f)] : Bindings) = σ at h
    cases h₁ : parameterListStep (encodingEnv p) (byValueObject tc).head σ with
    | ok σ₁ =>
      rw [h₁] at h
      have e₁ := parameterListStep_ok _ _ _ _ h₁
      simp only [Subst.bind_ok] at h
      cases h₂ : constraintStep (encodingEnv p) (byValueObject tc).constraint σ₁ with
      | ok σ₂ =>
        rw [h₂] at h
        have e₂ := constraintStep_ok _ _ _ _ h₂
        simp only [Subst.bind_ok] at h
        cases h₃ : nonDependentStep (encodingEnv p) (byValueObject tc).params [f, x] σ₂ with
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
    (hA : deduceTemplate (encodingEnv pA) (byValueObject tc) [] [f, x] = .ok sA)
    (hB : deduceTemplate (encodingEnv pB) (byValueObject tc) [] [f, x] = .ok sB)
    (hne : ∀ vA vB, (encodingEnv pA).instantiate tc x.ty.stripConst = .ok vA →
      (encodingEnv pB).instantiate tc x.ty.stripConst = .ok vB → policyOf vA ≠ policyOf vB) :
    sA ≠ sB := by
  obtain ⟨vA, hvA, hpA⟩ := byValue_policy tc f x pA hx hf hxF hxr hxd sA hA
  obtain ⟨vB, hvB, hpB⟩ := byValue_policy tc f x pB hx hf hxF hxr hxd sB hB
  intro e
  subst e
  rw [hpA] at hpB
  exact hne vA vB hvA hvB (Option.some.inj hpB)

end separation

/-- Stability at the call surface, per unit. An instance declared after
the call leaves it unchanged. An instance declared before it moves the
call as `call_stability` says, on the declarations that precede the
call. The single translation unit assumption is no longer built into
the environment: a call sees what precedes it, and a later instance its
use would select is the business of `late_insertion_verdict`. -/
theorem call_stability_unit (p : Program) (j pos : Nat) (tc : String) (h : Head) (pat : Ty)
    (r : Ranking Conv) (decls : List Decl) (f x : CallArg) (hpos : pos ≤ p.length)
    (hf : f.ty.isType = true) (hx : x.ty.isType = true)
    (hfF : f.ty.formed = true) (hxF : x.ty.formed = true)
    (hfr : f.ty.isRef = false) (hxr : x.ty.isRef = false) (hxd : x.ty.dependent = false)
    (hm : .functionTemplate (fmapObject tc) ∈ decls) :
    let p' := p.take j ++ .instance tc h pat :: p.drop j
    (pos < j → j ≤ p.length → callAt (encodingEnv ·) p' pos r decls [f, x] = callAt (encodingEnv ·) p pos r decls [f, x]) ∧
    (j ≤ pos →
      (p.take pos).any (fun | .lookup c => c = tc | _ => false) = true →
      (p.take pos).any (fun | .lookupHard c => c = tc | _ => false) = false →
      (∀ ft, .functionTemplate ft ∈ decls → ft ≠ fmapObject tc →
        deduceTemplate (encodingEnv (p'.take (pos + 1))) ft [] [f, x] =
          deduceTemplate (encodingEnv (p.take pos)) ft [] [f, x]) →
      callAt (encodingEnv ·) p' (pos + 1) r decls [f, x] = callAt (encodingEnv ·) p pos r decls [f, x] ∨
        (PatternMatches h pat x.ty.stripConst ∧
          (Program.selectInstance (p'.take (pos + 1)) tc x.ty.stripConst =
              Resolution.selected (Program.instancesOf (p.take j) tc).length ∨
            ∃ e, callAt (encodingEnv ·) p' (pos + 1) r decls [f, x] = .illFormed e))) := by
  intro p'
  refine ⟨fun hlt hj => callAt_insert_after _ p j pos _ r decls _ hj hlt, ?_⟩
  intro hj hsoft hhard hothers
  obtain ⟨e', e⟩ := take_insert_before p j pos (.instance tc h pat) hj hpos
  unfold callAt
  simp only [p'] at hothers ⊢
  rw [e', e] at hothers ⊢
  rw [e] at hsoft hhard
  exact call_stability (p.take j) ((p.drop j).take (pos - j)) tc h pat r decls f x hf hx hfF hxF hfr
    hxr hxd hsoft hhard hm hothers


end Overload.Typeclass
