-- Overload/Typeclass.lean                                            -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Program
import Overload.Ordering
import Overload.Ranking

/-!
# The typeclass encoding: canonical lookup

Canonical lookup is a variable template, `functor<T>`, whose partial
specializations are the instances. Which instance a type gets is decided
by partial specialization matching ([temp.spec.partial.match]) over the
instances the program declares, so the two lookup theorems of the plan are
theorems about `PartialOrdering.select`:

* coherence: lookup selects an instance exactly when that instance is the
  most specialized match, and at most one is; otherwise it reports the
  primary or ambiguity, and it never chooses silently (`coherence`,
  `MostSpecialized` and `mostSpecialized_unique`);
* stability: declaring one more instance, anywhere in the program, leaves
  lookup unchanged at every type the new instance does not match, and at
  a type it does match the lookup keeps its answer, moves to the new
  instance, or becomes ambiguous (`stability`). Lookups of other
  typeclasses do not move at all (`stability_other_typeclass`).

Neither theorem needs the single translation unit assumption or soft
failure of a missing instance. Both are about the variable template, where
a missing instance is the primary; they enter at the call surface, where
a lookup is instantiated and its outcome becomes soft or hard.

Instances are named by position among the instances of their typeclass,
so inserting one shifts the positions after it; `shiftAt` is that shift.
-/

namespace Overload

open PartialOrdering

namespace Program

/-- The instances of a typeclass in a program, as head and pattern, in
declaration order. -/
def instancesOf (p : Program) (tc : String) : List (Head × Ty) :=
  p.filterMap fun
    | .instance c h pat => if c = tc then some (h, pat) else none
    | _ => none

/-- Which instance of `tc` the type `a` selects, by partial specialization
matching and ordering: canonical lookup. -/
def selectInstance (p : Program) (tc : String) (a : Ty) : Resolution Nat :=
  select tc (p.instancesOf tc) a

theorem instancesOf_insert (p₁ p₂ : Program) (tc : String) (h : Head) (pat : Ty) :
    instancesOf (p₁ ++ .instance tc h pat :: p₂) tc = instancesOf p₁ tc ++ (h, pat) :: instancesOf p₂ tc := by
  simp [instancesOf, List.filterMap_append]

theorem instancesOf_append (p₁ p₂ : Program) (tc : String) :
    instancesOf (p₁ ++ p₂) tc = instancesOf p₁ tc ++ instancesOf p₂ tc := by
  simp [instancesOf, List.filterMap_append]

theorem instancesOf_insert_other (p₁ p₂ : Program) (tc tc' : String) (h : Head) (pat : Ty)
    (hne : tc ≠ tc') :
    instancesOf (p₁ ++ .instance tc h pat :: p₂) tc' = instancesOf (p₁ ++ p₂) tc' := by
  simp [instancesOf, List.filterMap_append, hne]

end Program

/-! ## Coherence -/

/-- Coherence: lookup selects an instance exactly when it is the most
specialized of the instances that match. With `mostSpecialized_unique`,
at most one instance is ever a candidate for selection, and with
`selectInstance_ne_illFormed` every other outcome is the primary or a
reported ambiguity. -/
theorem coherence (p : Program) (tc : String) (a : Ty) (i : Nat) :
    p.selectInstance tc a = .selected i ↔ MostSpecialized tc (p.instancesOf tc) a i := by
  rw [Program.selectInstance, select_iff]
  exact ⟨Selects.mostSpecialized_of_selected, Selects.of_mostSpecialized⟩

/-- Lookup is ambiguous exactly when two instances match and neither is
more specialized than all the others. -/
theorem coherence_ambiguous (p : Program) (tc : String) (a : Ty) (l : List Nat) :
    p.selectInstance tc a = .ambiguous l ↔
      l = matching (p.instancesOf tc) a ∧
      (∃ i j, i ≠ j ∧ Matches (p.instancesOf tc) a i ∧ Matches (p.instancesOf tc) a j) ∧
      ∀ i, ¬ MostSpecialized tc (p.instancesOf tc) a i := by
  rw [Program.selectInstance, select_iff]
  constructor
  · intro h
    cases h with
    | ambiguous htwo hnone => exact ⟨rfl, htwo, hnone⟩
  · rintro ⟨rfl, htwo, hnone⟩
    exact .ambiguous htwo hnone

/-- Lookup never makes the program ill-formed by itself; ambiguity is
reported as ambiguity. -/
theorem selectInstance_ne_illFormed (p : Program) (tc : String) (a : Ty) (r : Reason) :
    p.selectInstance tc a ≠ .illFormed r := by
  rw [Program.selectInstance, Ne, select_iff]
  intro h
  cases h

/-! ## Inserting an instance -/

/-- Where position `i` of a list lands once an entry is inserted at `k`. -/
def shiftAt (k i : Nat) : Nat := if i < k then i else i + 1

theorem shiftAt_ne (k i : Nat) : shiftAt k i ≠ k := by
  unfold shiftAt
  split <;> omega

theorem shiftAt_inj {k i j : Nat} (h : shiftAt k i = shiftAt k j) : i = j := by
  unfold shiftAt at h
  split at h <;> split at h <;> omega

/-- Every position of the longer list is the inserted one or a shifted
old one. -/
theorem shiftAt_cases (k i' : Nat) : i' = k ∨ ∃ i, i' = shiftAt k i := by
  rcases Nat.lt_trichotomy i' k with h | h | h
  · exact .inr ⟨i', by simp [shiftAt, h]⟩
  · exact .inl h
  · exact .inr ⟨i' - 1, by unfold shiftAt; split <;> omega⟩

theorem getElem?_insert_shift {α : Type} (l₁ l₂ : List α) (n : α) (i : Nat) :
    (l₁ ++ n :: l₂)[shiftAt l₁.length i]? = (l₁ ++ l₂)[i]? := by
  unfold shiftAt
  split
  · next h => rw [List.getElem?_append_left h, List.getElem?_append_left h]
  · next h =>
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    have : i + 1 - l₁.length = (i - l₁.length) + 1 := by omega
    rw [this, List.getElem?_cons_succ]

section insert

variable (tc : String) (l₁ l₂ : List (Head × Ty)) (n : Head × Ty) (arg : Ty)

theorem matches_insert_shift (i : Nat) :
    Matches (l₁ ++ n :: l₂) arg (shiftAt l₁.length i) ↔ Matches (l₁ ++ l₂) arg i := by
  simp only [Matches, getElem?_insert_shift]

theorem matches_insert_at :
    Matches (l₁ ++ n :: l₂) arg l₁.length ↔ PatternMatches n.1 n.2 arg := by
  obtain ⟨h, pat⟩ := n
  simp only [Matches, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨_, _, ⟨rfl, rfl⟩, hm⟩
    exact hm
  · exact fun hm => ⟨h, pat, ⟨rfl, rfl⟩, hm⟩

theorem matchesAt_insert_shift (i : Nat) :
    matchesAt (l₁ ++ n :: l₂) arg (shiftAt l₁.length i) = matchesAt (l₁ ++ l₂) arg i := by
  simp only [matchesAt, getElem?_insert_shift]

theorem beats_insert_shift (i j : Nat) :
    beats tc (l₁ ++ n :: l₂) (shiftAt l₁.length i) (shiftAt l₁.length j) = beats tc (l₁ ++ l₂) i j := by
  simp only [beats, getElem?_insert_shift]

theorem mostSpecialized_insert_shift {i : Nat}
    (h : MostSpecialized tc (l₁ ++ n :: l₂) arg (shiftAt l₁.length i)) :
    MostSpecialized tc (l₁ ++ l₂) arg i := by
  refine ⟨(matches_insert_shift l₁ l₂ n arg i).1 h.1, fun j hj hne => ?_⟩
  rw [← beats_insert_shift tc l₁ l₂ n]
  exact h.2 _ ((matches_insert_shift l₁ l₂ n arg j).2 hj) fun e => hne (shiftAt_inj e)

/-- The matching positions, when the inserted entry does not match, are
the old ones shifted. -/
theorem matching_insert (hn : ¬ PatternMatches n.1 n.2 arg) :
    matching (l₁ ++ n :: l₂) arg = (matching (l₁ ++ l₂) arg).map (shiftAt l₁.length) := by
  have hk : matchesAt (l₁ ++ n :: l₂) arg l₁.length = false := by
    cases h : matchesAt (l₁ ++ n :: l₂) arg l₁.length
    · rfl
    · exact absurd ((matches_insert_at l₁ l₂ n arg).1 (matchesAt_iff.1 h)) hn
  have hlen' : (l₁ ++ n :: l₂).length = l₁.length + (l₂.length + 1) := by simp
  have hlen : (l₁ ++ l₂).length = l₁.length + l₂.length := by simp
  simp only [matching, hlen', hlen, List.range_add, List.range_succ_eq_map, List.filter_append,
    List.map_cons, List.filter_cons, List.map_append, List.filter_map, List.map_map]
  simp only [Nat.add_zero, hk, Bool.false_eq_true, ite_false]
  congr 1
  · -- Below the insertion point nothing moves.
    have hlo : ∀ i ∈ List.range l₁.length, shiftAt l₁.length i = i := fun i hi => by
      simp [shiftAt, List.mem_range.1 hi]
    rw [List.map_congr_left (fun i hi => hlo i (List.mem_filter.1 hi).1), List.map_id']
    apply List.filter_congr
    intro i hi
    rw [← hlo i hi, matchesAt_insert_shift, hlo i hi]
  · -- Above it every position moves up by one.
    have hhi : ∀ j, shiftAt l₁.length (l₁.length + j) = l₁.length + (j + 1) := fun j => by
      unfold shiftAt
      split <;> omega
    simp only [Function.comp_def, hhi]
    congr 1
    apply List.filter_congr
    intro j _
    rw [← hhi, matchesAt_insert_shift]

/-- Inserting an entry the argument does not match changes the selection
only by the shift of positions. -/
theorem select_insert_unmatched (hn : ¬ PatternMatches n.1 n.2 arg) :
    select tc (l₁ ++ n :: l₂) arg = (select tc (l₁ ++ l₂) arg).map (shiftAt l₁.length) := by
  rw [select_iff]
  have hs := select_sound tc (l₁ ++ l₂) arg
  generalize select tc (l₁ ++ l₂) arg = r at hs
  have hk : ¬ Matches (l₁ ++ n :: l₂) arg l₁.length := fun h =>
    hn ((matches_insert_at l₁ l₂ n arg).1 h)
  -- A most specialized old match stays the most specialized, shifted.
  have hms : ∀ i, MostSpecialized tc (l₁ ++ l₂) arg i →
      MostSpecialized tc (l₁ ++ n :: l₂) arg (shiftAt l₁.length i) := fun i h => by
    refine ⟨(matches_insert_shift l₁ l₂ n arg i).2 h.1, fun j' hj' hne => ?_⟩
    rcases shiftAt_cases l₁.length j' with rfl | ⟨j, rfl⟩
    · exact absurd hj' hk
    · rw [beats_insert_shift]
      exact h.2 j ((matches_insert_shift l₁ l₂ n arg j).1 hj') fun e => hne (e ▸ rfl)
  cases hs with
  | unique i hm hu =>
    exact .of_mostSpecialized (hms i ⟨hm, fun j hj hne => absurd (hu j hj) hne⟩)
  | mostSpecialized i _ h => exact .of_mostSpecialized (hms i h)
  | ambiguous htwo hnone =>
    simp only [Resolution.map]
    rw [← matching_insert l₁ l₂ n arg hn]
    refine .ambiguous ?_ fun i' h => ?_
    · obtain ⟨i, j, hne, hi, hj⟩ := htwo
      exact ⟨_, _, fun e => hne (shiftAt_inj e), (matches_insert_shift l₁ l₂ n arg i).2 hi,
        (matches_insert_shift l₁ l₂ n arg j).2 hj⟩
    · rcases shiftAt_cases l₁.length i' with rfl | ⟨i, rfl⟩
      · exact hk h.1
      · exact hnone i (mostSpecialized_insert_shift tc l₁ l₂ n arg h)
  | primary hno =>
    refine .primary fun i' h => ?_
    rcases shiftAt_cases l₁.length i' with rfl | ⟨i, rfl⟩
    · exact hk h
    · exact hno i ((matches_insert_shift l₁ l₂ n arg i).1 h)

/-- Inserting an entry the argument matches either leaves the selection
as it was, up to the shift of positions, or moves it to the new entry or
to ambiguity. -/
theorem select_insert_matched :
    select tc (l₁ ++ n :: l₂) arg = (select tc (l₁ ++ l₂) arg).map (shiftAt l₁.length) ∨
    select tc (l₁ ++ n :: l₂) arg = .selected l₁.length ∨
    ∃ l, select tc (l₁ ++ n :: l₂) arg = .ambiguous l := by
  have hs := select_sound tc (l₁ ++ n :: l₂) arg
  generalize hr : select tc (l₁ ++ n :: l₂) arg = r at hs
  cases r with
  | selected i' =>
    rcases shiftAt_cases l₁.length i' with rfl | ⟨i, rfl⟩
    · exact .inr (.inl rfl)
    · refine .inl ?_
      have h := mostSpecialized_insert_shift tc l₁ l₂ n arg hs.mostSpecialized_of_selected
      rw [(select_iff _ _ _ _).2 (Selects.of_mostSpecialized h)]
      rfl
  | ambiguous l => exact .inr (.inr ⟨l, rfl⟩)
  | noMatch =>
    refine .inl ?_
    cases hs with
    | primary hno =>
      have hk : ¬ PatternMatches n.1 n.2 arg := fun h =>
        hno l₁.length ((matches_insert_at l₁ l₂ n arg).2 h)
      rw [← hr, select_insert_unmatched tc l₁ l₂ n arg hk]
  | illFormed _ => cases hs

end insert

/-! ## Stability -/

/-- Stability: declaring an instance of `tc` anywhere in a program changes
lookup of `tc` only at types the new instance matches, and there only to
the new instance or to ambiguity. A lookup that keeps its answer keeps it
up to the shift of instance positions past the insertion point. -/
theorem stability (p₁ p₂ : Program) (tc : String) (h : Head) (pat : Ty) (a : Ty) :
    let p := p₁ ++ p₂
    let p' := p₁ ++ .instance tc h pat :: p₂
    let k := (p₁.instancesOf tc).length
    p'.selectInstance tc a = (p.selectInstance tc a).map (shiftAt k) ∨
    (PatternMatches h pat a ∧
      (p'.selectInstance tc a = .selected k ∨ ∃ l, p'.selectInstance tc a = .ambiguous l)) := by
  intro p p' k
  simp only [p, p', k, Program.selectInstance]
  rw [Program.instancesOf_insert, Program.instancesOf_append]
  by_cases hn : PatternMatches h pat a
  · rcases select_insert_matched tc (p₁.instancesOf tc) (p₂.instancesOf tc) (h, pat) a with e | e | e
    · exact .inl e
    · exact .inr ⟨hn, .inl e⟩
    · exact .inr ⟨hn, .inr e⟩
  · exact .inl (select_insert_unmatched tc _ _ (h, pat) a hn)

/-- Declaring an instance of one typeclass does not move lookup of
another. -/
theorem stability_other_typeclass (p₁ p₂ : Program) (tc tc' : String) (h : Head) (pat : Ty)
    (a : Ty) (hne : tc ≠ tc') :
    (p₁ ++ .instance tc h pat :: p₂).selectInstance tc' a = (p₁ ++ p₂).selectInstance tc' a := by
  simp only [Program.selectInstance, Program.instancesOf_insert_other _ _ _ _ _ _ hne]

/-! ## The program's environment, and the operation object -/

/-- Does a type have the shape of an instance: an instance and the
pinned instance type have `fmap`, and the primary, `std::false_type`,
has not. -/
def instanceShape : Ty → Bool
  | .spec "instance_of" _ | .named "pinned_instance" => true
  | _ => false

/-- The shape constraint on a type, or on the type of a constant
argument, `decltype(TC)`, which satisfaction evaluates. -/
def fmapShape (t : Ty) : Bool :=
  instanceShape (match t with | .typeOf e => e.typeOfValue | t => t)

/-- The environment a program defines: the lookups it declares, hard or
soft, with their instances; `has_instance` and the case's atomic table
and the operation object's call through its instance, `fmap_call`, as
the atomic constraints, with the case's table for any other; and
convertibility as the existence of an implicit conversion sequence under
the program's ranking (`Program.ics`). -/
def Env.ofProgram (p : Program) (atomics : List (String × List Ty × Bool) := []) : Env :=
  { instantiate := fun n a =>
      let hard := p.any fun | .lookupHard c => c = n | _ => false
      let soft := p.any fun | .lookup c => c = n | _ => false
      match p.selectInstance n a with
      | .selected i => .ok (.spec' "instance_of" [a, .value (.int i)])
      | .ambiguous _ => .hard s!"ambiguous partial specializations of {n}<{repr a}>"
      | .illFormed r => .hard r
      | .noMatch =>
        if hard then .hard s!"static_assert in the primary {n}<{repr a}>"
        else if soft then .ok (.named "std::false_type")
        else .soft s!"no variable template {n}"
    atomic := fun e args =>
      match e, args with
      | "has_instance", [.named c, a] => .ok ((p.selectInstance c a).toOption.isSome)
      -- The operation object's constraint, the call through the instance:
      -- an instance has the operation, and the primary, `std::false_type`,
      -- does not.
      | "fmap_call", [.ref (.lookup c a), _, _] => .ok ((p.selectInstance c a).toOption.isSome)
      | "fmap_shape", [t] => .ok (fmapShape t)
      | _, _ =>
        match atomics.find? fun (e', args', _) => e' == e && args' == args with
        | some (_, _, b) => .ok b
        | none => .soft s!"unknown atomic constraint {e}"
    convertible := fun a t => .ok (p.ics a t).isSome }

/-- The operation object `fmap` of beman.transpose, for the typeclass
`tc`: `template <class F, class T, const auto &TC =
tc<std::remove_cvref_t<T>>> requires requires { TC.fmap(...); } auto
operator()(F &&, T &&) const`. A call of the object is resolved as a call
of this one template. -/
def fmapObject (tc : String) : FunctionTemplate :=
  { name := "fmap"
    head :=
      [ { kind := .type }, { kind := .type }
      , { kind := .const (.lref (.const (.named "auto")))
          default := some (.ref (.lookup tc (.removeCvref (.param 1)))) } ]
    params := [.rref (.param 0), .rref (.param 1)]
    constraint := some (.atomic "fmap_call" [.param 2, .param 0, .param 1]) }

/-- A type that forming leaves as it is: no reference, pointer or
`const` applied to a reference, and none of the constructs forming
computes or instantiates. -/
def Ty.formed : Ty → Bool
  | .named _ | .nil | .value _ | .param _ => true
  | .const t | .ptr t | .lref t | .rref t => t.formed && !t.isRef
  | .spec _ as => as.formed
  | .cons a as => a.formed && as.formed
  | _ => false

theorem form_formed (env : Env) (t : Ty) (h : t.formed = true) : form env t = .ok t := by
  induction t with
  | named _ | nil | value _ | param _ => rfl
  | const t ih =>
    simp only [Ty.formed, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp [form, ih h.1, formConst, h.2]
  | ptr t ih =>
    simp only [Ty.formed, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp [form, ih h.1, formPtr, h.2]
  | lref t ih | rref t ih =>
    simp only [Ty.formed, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [form, ih h.1, Subst.bind_eq, Subst.bind_ok, Subst.pure_eq]
    cases t <;> simp_all [Ty.collapse, Ty.isRef]
  | spec c as ih =>
    simp only [Ty.formed] at h
    simp [form, ih h]
  | cons a as iha ihas =>
    simp only [Ty.formed, Bool.and_eq_true] at h
    simp [form, iha h.1, ihas h.2]
  | _ => simp [Ty.formed] at h

/-- The type a forwarding reference deduces from an argument: the
argument's type, as an lvalue reference for an lvalue. -/
def forwarded (a : CallArg) : Ty := if a.lvalue then .lref a.ty else a.ty

theorem fmapObject_call (tc : String) (f x : CallArg) (hf : f.ty.isType = true)
    (hx : x.ty.isType = true) :
    (explicitStep (fmapObject tc).head [] >>= callStep (fmapObject tc).params [f, x]) =
      .ok [(1, forwarded x), (0, forwarded f)] := by
  have h0 : Ty.collapse (.rref (.param 0)) = .rref (.param 0) := rfl
  have h1 : Ty.collapse (.rref (.param 1)) = .rref (.param 1) := rfl
  have hl : ∀ t : Ty, (Ty.lref t).isType = true := fun _ => rfl
  cases hlf : f.lvalue <;> cases hlx : x.lvalue <;>
    simp [h0, h1, hl, fmapObject, explicitStep, explicitStep.go, callStep, deduceCall, deduceParam, adjustP,
      adjustA, isForwardingRef, Ty.isRef, Ty.referred, Ty.dependent, Ty.subst, Bindings.lookup,
      deduceTy, bindArg, forwarded, hlf, hlx, hf, hx]

theorem forwarded_formed (a : CallArg) (h : a.ty.formed = true) (hr : a.ty.isRef = false) :
    (forwarded a).formed = true := by
  unfold forwarded
  split <;> simp [Ty.formed, h, hr]

theorem forwarded_key (a : CallArg) (hr : a.ty.isRef = false) :
    (forwarded a).referred.stripConst = a.ty.stripConst := by
  unfold forwarded
  split
  · rfl
  · cases h : a.ty <;> simp_all [Ty.referred, Ty.isRef]

theorem forwarded_dependent (a : CallArg) : (forwarded a).dependent = a.ty.dependent := by
  unfold forwarded
  split <;> rfl

theorem forwarded_isType (a : CallArg) (h : a.ty.isType = true) : (forwarded a).isType = true := by
  unfold forwarded
  split
  · rfl
  · exact h

/-- A parameter bound to a type is replaced by it. -/
theorem subst_param_type (σ : Bindings) (i : ParamIdx) (t : Ty) (hl : σ.lookup i = some t)
    (ht : t.isType = true) : Ty.subst σ (.param i) = t := by
  simp only [Ty.subst, hl]
  split <;> simp_all [Ty.isType]

theorem dependent_stripConst (t : Ty) : t.stripConst.dependent = t.dependent := by
  cases t <;> rfl

/-- The specialization deduced for a call of the operation object. Its
instance argument is the reference to the lookup, not the instance
selected, so it is the same whichever instance that is. -/
def fmapSpec (tc : String) (f x : CallArg) : Specialization :=
  { template := fmapObject tc
    args := [(2, .ref (.lookup tc x.ty.stripConst)), (1, forwarded x), (0, forwarded f)]
    params := [Ty.collapse (.rref (forwarded f)), Ty.collapse (.rref (forwarded x))]
    ret := .named "void" }

/-- The outcome of deducing the operation object, given the outcome of
instance lookup at its key. -/
def fmapOutcome (tc : String) (f x : CallArg) : Resolution Nat → Subst Specialization
  | .selected _ => .ok (fmapSpec tc f x)
  | .noMatch => .soft "associated constraints not satisfied"
  | .ambiguous _ => .hard s!"ambiguous partial specializations of {tc}<{repr x.ty.stripConst}>"
  | .illFormed r => .hard r

section fmapObject

variable (p : Program) (tc : String) (f x : CallArg)

/-- The bindings after deduction from the call. -/
private abbrev σ₀ : Bindings := [(1, forwarded x), (0, forwarded f)]

/-- The lookup key: the container's type with cv and reference removed. -/
private abbrev key : Ty := x.ty.stripConst

theorem fmapObject_defaults (env : Env) (hx : x.ty.isType = true) (hxF : x.ty.formed = true)
    (hxr : x.ty.isRef = false) (hxd : x.ty.dependent = false) :
    defaultsStep env (fmapObject tc).head (σ₀ f x) =
      (env.instantiate tc (key x)).bind fun _ => .ok ((2, .ref (.lookup tc (key x))) :: σ₀ f x) := by
  have h1 : Ty.subst (σ₀ f x) (.param 1) = forwarded x :=
    subst_param_type _ _ _ (by simp [Bindings.lookup]) (forwarded_isType x hx)
  have hd : Ty.subst (σ₀ f x) (.ref (.lookup tc (.removeCvref (.param 1)))) =
      .ref (.lookup tc (.removeCvref (forwarded x))) := by
    show Ty.ref (Ty.lookup tc (Ty.removeCvref (Ty.subst (σ₀ f x) (.param 1)))) = _
    rw [h1]
  have hform : form env (forwarded x) = .ok (forwarded x) :=
    form_formed env _ (forwarded_formed x hxF hxr)
  simp only [defaultsStep, defaultsStep.go, fmapObject, Bindings.lookup, List.find?]
  simp only [decide_true, decide_false, Option.map_some, Option.map_none, Nat.reduceEqDiff,
    reduceCtorEq]
  rw [hd]
  simp [form, hform, forwarded_dependent, hxd, forwarded_key x hxr, dependent_stripConst]
  cases env.instantiate tc x.ty.stripConst <;> rfl

theorem collapse_rref_forwarded_formed (a : CallArg) (h : a.ty.formed = true)
    (hr : a.ty.isRef = false) : (Ty.collapse (.rref (forwarded a))).formed = true := by
  unfold forwarded
  split
  · simp [Ty.collapse, Ty.formed, h, hr]
  · cases ha : a.ty <;> simp_all [Ty.collapse, Ty.formed, Ty.isRef]

/-- After the defaults, the steps that remain succeed exactly when the
constraint, the call through the instance, holds; otherwise the
constraint step fails softly. -/
theorem fmapObject_rest (hf : f.ty.isType = true) (hx : x.ty.isType = true)
    (hfF : f.ty.formed = true) (hxF : x.ty.formed = true)
    (hfr : f.ty.isRef = false) (hxr : x.ty.isRef = false) :
    let env := Env.ofProgram p
    let σ₁ := (2, Ty.ref (.lookup tc (key x))) :: σ₀ f x
    (parameterListStep env (fmapObject tc).head σ₁ >>= constraintStep env (fmapObject tc).constraint
        >>= nonDependentStep env (fmapObject tc).params [f, x] >>= functionTypeStep env (fmapObject tc)) =
      if (p.selectInstance tc (key x)).toOption.isSome then .ok (fmapSpec tc f x)
      else .soft "associated constraints not satisfied" := by
  intro env σ₁
  have h0 : Ty.subst σ₁ (.param 0) = forwarded f :=
    subst_param_type _ _ _ (by simp [σ₁, Bindings.lookup]) (forwarded_isType f hf)
  have h1 : Ty.subst σ₁ (.param 1) = forwarded x :=
    subst_param_type _ _ _ (by simp [σ₁, Bindings.lookup]) (forwarded_isType x hx)
  have h2 : Ty.subst σ₁ (.param 2) = .ref (.lookup tc (key x)) := by
    simp [Ty.subst, σ₁, Bindings.lookup]
  have hparams : formAll env [Ty.subst σ₁ (.rref (.param 0)), Ty.subst σ₁ (.rref (.param 1))] =
      .ok [Ty.collapse (.rref (forwarded f)), Ty.collapse (.rref (forwarded x))] := by
    show formAll env [Ty.collapse (.rref (Ty.subst σ₁ (.param 0))),
      Ty.collapse (.rref (Ty.subst σ₁ (.param 1)))] = _
    rw [h0, h1]
    simp [formAll, form_formed env _ (collapse_rref_forwarded_formed f hfF hfr),
      form_formed env _ (collapse_rref_forwarded_formed x hxF hxr)]
  have hplist : parameterListStep env (fmapObject tc).head σ₁ = .ok σ₁ := by
    rfl
  have hsat : Constraint.satisfied env.atomic σ₁ (.atomic "fmap_call" [.param 2, .param 0, .param 1]) =
      .ok (p.selectInstance tc (key x)).toOption.isSome := by
    simp only [Constraint.satisfied, List.map, h0, h1, h2]
    simp [env, Env.ofProgram]
  rw [hplist]
  simp only [Subst.bind_eq, Subst.bind_ok, constraintStep, fmapObject, hsat]
  cases (p.selectInstance tc (key x)).toOption.isSome
  · simp
  · have hnd : nonDependentStep env [(Ty.param 0).rref, (Ty.param 1).rref] [f, x] σ₁ = .ok σ₁ := rfl
    simp only [↓reduceIte, Subst.pure_eq, Subst.bind_ok, hnd, functionTypeStep, List.map]
    rw [hparams]
    rfl

/-- Deducing the operation object for a call is a function of instance
lookup at the container's type with cv and reference removed, and of
nothing else in the program. -/
theorem fmapObject_deduce (hf : f.ty.isType = true) (hx : x.ty.isType = true)
    (hfF : f.ty.formed = true) (hxF : x.ty.formed = true)
    (hfr : f.ty.isRef = false) (hxr : x.ty.isRef = false) (hxd : x.ty.dependent = false)
    (hsoft : p.any (fun | .lookup c => c = tc | _ => false) = true)
    (hhard : p.any (fun | .lookupHard c => c = tc | _ => false) = false) :
    deduceTemplate (Env.ofProgram p) (fmapObject tc) [] [f, x] =
      fmapOutcome tc f x (p.selectInstance tc x.ty.stripConst) := by
  have hs := fmapObject_rest p tc f x hf hx hfF hxF hfr hxr
  simp only [Subst.bind_eq] at hs
  have hr : deduceTemplate (Env.ofProgram p) (fmapObject tc) [] [f, x] =
      ((Env.ofProgram p).instantiate tc (key x)).bind fun _ =>
      (parameterListStep (Env.ofProgram p) (fmapObject tc).head ((2, Ty.ref (.lookup tc (key x))) :: σ₀ f x)
        >>= constraintStep (Env.ofProgram p) (fmapObject tc).constraint
        >>= nonDependentStep (Env.ofProgram p) (fmapObject tc).params [f, x]
        >>= functionTypeStep (Env.ofProgram p) (fmapObject tc)) := by
    simp only [deduceTemplate]
    rw [fmapObject_call tc f x hf hx]
    simp only [Subst.bind_eq, Subst.bind_ok]
    rw [fmapObject_defaults tc f x _ hx hxF hxr hxd]
    cases (Env.ofProgram p).instantiate tc (key x) <;> rfl
  have hinst : (Env.ofProgram p).instantiate tc (key x) =
      match p.selectInstance tc (key x) with
      | .selected i => .ok (.spec' "instance_of" [key x, .value (.int i)])
      | .ambiguous _ => .hard s!"ambiguous partial specializations of {tc}<{repr (key x)}>"
      | .illFormed r => .hard r
      | .noMatch => .ok (.named "std::false_type") := by
    simp only [Env.ofProgram, hsoft, hhard]
    split <;> simp
  rw [hr, hinst]
  cases hl : p.selectInstance tc (key x) with
  | selected i =>
    simp only [Subst.bind_eq, Subst.bind_ok]
    rw [hs, hl]
    rfl
  | noMatch =>
    simp only [Subst.bind_eq, Subst.bind_ok]
    rw [hs, hl]
    rfl
  | ambiguous l => rfl
  | illFormed r => rfl

/-- The operation object at the call surface. For a program whose lookup
has the soft default, `std::false_type`, deducing the operation object
for a call follows instance lookup at the container's type with cv and
reference removed. It succeeds when an instance is selected. A missing
instance is a deduction failure, so the call is merely not viable: the
soft-failure obligation, discharged by construction. Only an ambiguous
lookup is a hard error. The arguments are formed, non-reference,
non-dependent types, as the arguments of a call are. -/
theorem fmapObject_outcome (hf : f.ty.isType = true) (hx : x.ty.isType = true)
    (hfF : f.ty.formed = true) (hxF : x.ty.formed = true)
    (hfr : f.ty.isRef = false) (hxr : x.ty.isRef = false) (hxd : x.ty.dependent = false)
    (hsoft : p.any (fun | .lookup c => c = tc | _ => false) = true)
    (hhard : p.any (fun | .lookupHard c => c = tc | _ => false) = false) :
    let r := deduceTemplate (Env.ofProgram p) (fmapObject tc) [] [f, x]
    (∀ i, p.selectInstance tc x.ty.stripConst = .selected i → ∃ s, r = .ok s) ∧
    (p.selectInstance tc x.ty.stripConst = .noMatch → ∃ e, r = .soft e) ∧
    (∀ l, p.selectInstance tc x.ty.stripConst = .ambiguous l → ∃ e, r = .hard e) := by
  intro r
  have hd : r = _ := fmapObject_deduce p tc f x hf hx hfF hxF hfr hxr hxd hsoft hhard
  refine ⟨fun i hi => ?_, fun hn => ?_, fun l hl => ?_⟩
  · rw [hd, hi]; exact ⟨_, rfl⟩
  · rw [hd, hn]; exact ⟨_, rfl⟩
  · rw [hd, hl]; exact ⟨_, rfl⟩

end fmapObject

/-! ## Stability at the call surface -/

theorem fmapOutcome_map (tc : String) (f x : CallArg) (g : Nat → Nat) (r : Resolution Nat) :
    fmapOutcome tc f x (r.map g) = fmapOutcome tc f x r := by
  cases r <;> rfl

/-- Declaring an instance does not change which lookups a program
declares. -/
theorem any_insert_instance (p₁ p₂ : Program) (tc : String) (h : Head) (pat : Ty)
    (g : Decl → Bool) (hg : g (.instance tc h pat) = false) :
    (p₁ ++ .instance tc h pat :: p₂).any g = (p₁ ++ p₂).any g := by
  simp [List.any_append, hg]

/-- Stability of a call of the operation object. Declaring an instance
anywhere in a program leaves the resolution of the call unchanged unless
the new instance matches the container's type with cv and reference
removed. When it matches, the operation object becomes viable through the
new instance, or lookup is ambiguous and, under the text, the call is
ill-formed. The other candidates are any non-template functions and any
templates whose deduction does not consult the lookup; that is the
hypothesis `hothers`, which a template that also looks up `tc` would have
to meet through stability of its own lookups. -/
theorem call_stability (p₁ p₂ : Program) (tc : String) (h : Head) (pat : Ty) (r : Ranking Conv)
    (decls : List Decl) (f x : CallArg)
    (hf : f.ty.isType = true) (hx : x.ty.isType = true)
    (hfF : f.ty.formed = true) (hxF : x.ty.formed = true)
    (hfr : f.ty.isRef = false) (hxr : x.ty.isRef = false) (hxd : x.ty.dependent = false)
    (hsoft : (p₁ ++ p₂).any (fun | .lookup c => c = tc | _ => false) = true)
    (hhard : (p₁ ++ p₂).any (fun | .lookupHard c => c = tc | _ => false) = false)
    (hm : .functionTemplate (fmapObject tc) ∈ decls) :
    let p := p₁ ++ p₂
    let p' := p₁ ++ .instance tc h pat :: p₂
    (∀ ft, .functionTemplate ft ∈ decls → ft ≠ fmapObject tc →
      deduceTemplate (Env.ofProgram p') ft [] [f, x] = deduceTemplate (Env.ofProgram p) ft [] [f, x]) →
    resolve .text (Env.ofProgram p') r decls [f, x] = resolve .text (Env.ofProgram p) r decls [f, x] ∨
    (PatternMatches h pat x.ty.stripConst ∧
      (p'.selectInstance tc x.ty.stripConst = .selected (p₁.instancesOf tc).length ∨
        ∃ e, resolve .text (Env.ofProgram p') r decls [f, x] = .illFormed e)) := by
  intro p p' hothers
  have hsoft' : p'.any (fun | .lookup c => c = tc | _ => false) = true := by
    rw [any_insert_instance _ _ _ _ _ _ rfl]; exact hsoft
  have hhard' : p'.any (fun | .lookupHard c => c = tc | _ => false) = false := by
    rw [any_insert_instance _ _ _ _ _ _ rfl]; exact hhard
  have hd := fmapObject_deduce p tc f x hf hx hfF hxF hfr hxr hxd hsoft hhard
  have hd' := fmapObject_deduce p' tc f x hf hx hfF hxF hfr hxr hxd hsoft' hhard'
  have hcongr : deduceTemplate (Env.ofProgram p') (fmapObject tc) [] [f, x] =
      deduceTemplate (Env.ofProgram p) (fmapObject tc) [] [f, x] →
      resolve .text (Env.ofProgram p') r decls [f, x] = resolve .text (Env.ofProgram p) r decls [f, x] :=
    fun he => resolve_congr _ _ _ r decls _ fun ft hft => by
      by_cases hft' : ft = fmapObject tc
      · subst hft'; exact he
      · exact hothers ft hft hft'
  rcases stability p₁ p₂ tc h pat x.ty.stripConst with e | ⟨hmatch, e | ⟨l, e⟩⟩
  · refine .inl (hcongr ?_)
    rw [hd', hd, e, fmapOutcome_map]
  · exact .inr ⟨hmatch, .inl e⟩
  · refine .inr ⟨hmatch, .inr ?_⟩
    rw [e] at hd'
    exact resolve_text_hard _ r decls _ _ _ hm hd'

/-! ## Pinning -/

/-- The pinning pattern of beman.transpose's examples: a user function
template whose trailing reference parameter defaults to the lookup,
`template <class C, const auto &TC = tc<C>> void name(const C &)`. The
body calls through `TC`, and there is no constraint. A caller pins an
instance by specifying `TC` explicitly. -/
def pinTemplate (tc name : String) : FunctionTemplate :=
  { name
    head :=
      [ { kind := .type }
      , { kind := .const (.lref (.const (.named "auto")))
          default := some (.ref (.lookup tc (.param 0))) } ]
    params := [.lref (.const (.param 0))] }

/-- The specialization of the pinning template at `C = c` with instance
argument `inst`. -/
def pinSpec (tc name : String) (c inst : Ty) : Specialization :=
  { template := pinTemplate tc name, args := [(1, inst), (0, c)]
    params := [.lref (.const c)], ret := .named "void" }

/-- Pinned: with `C` and the instance specified, deduction never
substitutes the default, so it never instantiates the lookup. The
outcome is the same in every environment, whatever the program's
instances are, including none and an ambiguous pair. -/
theorem pinned_deduce (env : Env) (tc name o : String) (c : Ty) (x : CallArg)
    (hc : c.isType = true) (hcd : c.dependent = false) (hcF : c.formed = true)
    (hcr : c.isRef = false) :
    deduceTemplate env (pinTemplate tc name) [c, .ref (.named o)] [x] =
      .ok (pinSpec tc name c (.ref (.named o))) := by
  have hsub : Ty.subst [(1, .ref (.named o)), (0, c)] (.lref (.const (.param 0))) =
      .lref (.const c) := by
    have h0 : Ty.subst [(1, .ref (.named o)), (0, c)] (.param 0) = c :=
      subst_param_type _ _ _ (by simp [Bindings.lookup]) hc
    show Ty.collapse (.lref (.const (Ty.subst _ (.param 0)))) = _
    rw [h0]
    rfl
  have hform : form env (.lref (.const c)) = .ok (.lref (.const c)) :=
    form_formed env _ (by simp [Ty.formed, hcF, Ty.isRef] at *; exact hcr)
  have hcall : callStep (pinTemplate tc name).params [x] [(1, .ref (.named o)), (0, c)] =
      .ok [(1, .ref (.named o)), (0, c)] := by
    simp only [callStep, pinTemplate, List.map, hsub, deduceCall, deduceParam, Ty.dependent, hcd]
    rfl
  have hexp : explicitStep (pinTemplate tc name).head [c, .ref (.named o)] =
      .ok [(1, .ref (.named o)), (0, c)] := by
    simp [explicitStep, explicitStep.go, pinTemplate, kindMatches, hc]
    rfl
  have hdef : defaultsStep env (pinTemplate tc name).head [(1, .ref (.named o)), (0, c)] =
      .ok [(1, .ref (.named o)), (0, c)] := by
    simp [defaultsStep, defaultsStep.go, Bindings.lookup, pinTemplate]
  have hft : functionTypeStep env (pinTemplate tc name) [(1, .ref (.named o)), (0, c)] =
      .ok (pinSpec tc name c (.ref (.named o))) := by
    simp only [functionTypeStep, pinTemplate, List.map, hsub, formAll, hform, Subst.bind_eq,
      Subst.bind_ok, Subst.pure_eq]
    rfl
  simp only [deduceTemplate, Subst.bind_eq]
  rw [hexp, Subst.bind_ok, hcall, Subst.bind_ok, hdef, Subst.bind_ok]
  exact hft

/-- The outcome of deducing the unpinned template, given the outcome of
instance lookup at its key. -/
def pinOutcome (tc name : String) (c : Ty) : Resolution Nat → Subst Specialization
  | .selected _ | .noMatch => .ok (pinSpec tc name c (.ref (.lookup tc c)))
  | .ambiguous _ => .hard s!"ambiguous partial specializations of {tc}<{repr c}>"
  | .illFormed r => .hard r

theorem pin_call (tc name : String) (x : CallArg) (hx : x.ty.isType = true)
    (hk : x.ty.stripConst.isType = true) :
    callStep (pinTemplate tc name).params [x] [] = .ok [(0, x.ty.stripConst)] := by
  cases h : x.ty <;> simp_all [callStep, pinTemplate, deduceCall, deduceParam, adjustP, adjustA,
    isForwardingRef, Ty.isRef, Ty.referred, Ty.dependent, Ty.subst, Bindings.lookup, deduceTy,
    bindArg, Ty.stripConst, Ty.collapse] <;> rfl

/-- Unpinned, the pinning template takes the canonical instance, but it
has no constraint: a missing instance binds the primary and the call is
viable. The soft-failure obligation is not discharged by the pattern; a
missing instance becomes an error in the body. Only an ambiguous lookup
fails deduction, and it fails hard. -/
theorem unpinned_deduce (p : Program) (tc name : String) (x : CallArg)
    (hx : x.ty.isType = true) (hk : x.ty.stripConst.isType = true)
    (hkF : x.ty.stripConst.formed = true) (hkr : x.ty.stripConst.isRef = false)
    (hkd : x.ty.stripConst.dependent = false)
    (hsoft : p.any (fun | .lookup c => c = tc | _ => false) = true)
    (hhard : p.any (fun | .lookupHard c => c = tc | _ => false) = false) :
    deduceTemplate (Env.ofProgram p) (pinTemplate tc name) [] [x] =
      pinOutcome tc name x.ty.stripConst (p.selectInstance tc x.ty.stripConst) := by
  generalize hc : x.ty.stripConst = c at *
  have h0 : Ty.subst [(0, c)] (.param 0) = c := subst_param_type _ _ _ (by simp [Bindings.lookup]) hk
  have hσ : ∀ σ : Bindings, σ = [(1, .ref (.lookup tc c)), (0, c)] →
      Ty.subst σ (.lref (.const (.param 0))) = .lref (.const c) := by
    rintro σ rfl
    have h0' : Ty.subst [(1, .ref (.lookup tc c)), (0, c)] (.param 0) = c :=
      subst_param_type _ _ _ (by simp [Bindings.lookup]) hk
    show Ty.collapse (.lref (.const (Ty.subst _ (.param 0)))) = _
    rw [h0']
    rfl
  have hform : ∀ env, form env (.lref (.const c)) = .ok (.lref (.const c)) := fun env =>
    form_formed env _ (by simp [Ty.formed, hkF, Ty.isRef] at *; exact hkr)
  have hdef : defaultsStep (Env.ofProgram p) (pinTemplate tc name).head [(0, c)] =
      ((Env.ofProgram p).instantiate tc c).bind fun _ => .ok [(1, .ref (.lookup tc c)), (0, c)] := by
    have hd : Ty.subst [(0, c)] (.ref (.lookup tc (.param 0))) = .ref (.lookup tc c) := by
      show Ty.ref (Ty.lookup tc (Ty.subst _ (.param 0))) = _
      rw [h0]
    simp only [defaultsStep, defaultsStep.go, pinTemplate, Bindings.lookup, List.find?]
    simp only [decide_true, decide_false, Option.map_some, Option.map_none,
      reduceCtorEq]
    rw [hd]
    simp [form, form_formed _ _ hkF, hkd]
    cases (Env.ofProgram p).instantiate tc c <;> rfl
  have hft : functionTypeStep (Env.ofProgram p) (pinTemplate tc name) [(1, .ref (.lookup tc c)), (0, c)] =
      .ok (pinSpec tc name c (.ref (.lookup tc c))) := by
    simp only [functionTypeStep, pinTemplate, List.map, hσ _ rfl, formAll, hform, Subst.bind_eq,
      Subst.bind_ok, Subst.pure_eq]
    rfl
  have hinst : (Env.ofProgram p).instantiate tc c =
      match p.selectInstance tc c with
      | .selected i => .ok (.spec' "instance_of" [c, .value (.int i)])
      | .ambiguous _ => .hard s!"ambiguous partial specializations of {tc}<{repr c}>"
      | .illFormed r => .hard r
      | .noMatch => .ok (.named "std::false_type") := by
    simp only [Env.ofProgram, hsoft, hhard]
    split <;> simp
  have hcall := pin_call tc name x hx (hc ▸ hk)
  rw [hc] at hcall
  simp only [deduceTemplate, Subst.bind_eq]
  rw [show explicitStep (pinTemplate tc name).head [] = .ok [] from rfl, Subst.bind_ok, hcall,
    Subst.bind_ok, hdef, hinst]
  cases p.selectInstance tc c with
  | selected i => exact hft
  | noMatch => exact hft
  | ambiguous l => rfl
  | illFormed r => rfl

/-! ## The by-value route -/

/-- The by-value route of beman.transpose, `traverse`'s `POLICY`, reduced
to `fmap`: `template <class F, class T, class P =
std::remove_cvref_t<decltype(tc<std::remove_cvref_t<T>>)>> requires
fmap_shape<P> void fmap_with(F &&, T &&, P = P{})`. A caller supplies an
instance by passing it as the third argument, and the instance enters
the specialization by its type. The constraint checks the shape of the
type, which is what makes a missing instance a soft failure. -/
def byValueObject (tc : String) : FunctionTemplate :=
  { name := "fmap_with"
    head :=
      [ { kind := .type }, { kind := .type }
      , { kind := .type, default := some (.typeOf (.lookup tc (.removeCvref (.param 1)))) } ]
    params := [.rref (.param 0), .rref (.param 1), .param 2]
    defaultArgs := 1
    constraint := some (.atomic "fmap_shape" [.param 2]) }

theorem byValue_call_omitted (tc : String) (f x : CallArg) (hf : f.ty.isType = true)
    (hx : x.ty.isType = true) :
    (explicitStep (byValueObject tc).head [] >>= callStep (byValueObject tc).params [f, x]) =
      .ok [(1, forwarded x), (0, forwarded f)] := by
  have h0 : Ty.collapse (.rref (.param 0)) = .rref (.param 0) := rfl
  have h1 : Ty.collapse (.rref (.param 1)) = .rref (.param 1) := rfl
  have hl : ∀ t : Ty, (Ty.lref t).isType = true := fun _ => rfl
  cases hlf : f.lvalue <;> cases hlx : x.lvalue <;>
    simp [h0, h1, hl, byValueObject, explicitStep, explicitStep.go, callStep, deduceCall, deduceParam,
      adjustP, adjustA, isForwardingRef, Ty.isRef, Ty.referred, Ty.dependent, Ty.subst, Bindings.lookup,
      deduceTy, bindArg, forwarded, hlf, hlx, hf, hx]

theorem formed_stripConst (t : Ty) (h : t.formed = true) : t.stripConst.formed = true := by
  cases t <;> simp_all [Ty.stripConst, Ty.formed]

/-- The specialization of the by-value route with policy type `v`. Its
policy argument is the instance's type, so it names the instance. -/
def byValueSpec (tc : String) (f x : CallArg) (v : Ty) : Specialization :=
  { template := byValueObject tc, args := [(2, v), (1, forwarded x), (0, forwarded f)]
    params := [Ty.collapse (.rref (forwarded f)), Ty.collapse (.rref (forwarded x)), v]
    ret := .named "void" }

section byValue

variable (p : Program) (tc : String) (f x : CallArg)

theorem byValue_defaults (env : Env) (hx : x.ty.isType = true) (hxF : x.ty.formed = true)
    (hxr : x.ty.isRef = false) (hxd : x.ty.dependent = false) :
    defaultsStep env (byValueObject tc).head [(1, forwarded x), (0, forwarded f)] =
      (env.instantiate tc x.ty.stripConst).bind fun v =>
        .ok ((2, if v.dependent then .typeOf v else v.typeOfValue) :: [(1, forwarded x), (0, forwarded f)]) := by
  have h1 : Ty.subst [(1, forwarded x), (0, forwarded f)] (.param 1) = forwarded x :=
    subst_param_type _ _ _ (by simp [Bindings.lookup]) (forwarded_isType x hx)
  have hd : Ty.subst [(1, forwarded x), (0, forwarded f)] (.typeOf (.lookup tc (.removeCvref (.param 1)))) =
      .typeOf (.lookup tc (.removeCvref (forwarded x))) := by
    show Ty.typeOf (Ty.lookup tc (Ty.removeCvref (Ty.subst _ (.param 1)))) = _
    rw [h1]
  have hform : form env (forwarded x) = .ok (forwarded x) :=
    form_formed env _ (forwarded_formed x hxF hxr)
  simp only [defaultsStep, defaultsStep.go, byValueObject, Bindings.lookup, List.find?]
  simp only [decide_true, decide_false, Option.map_some, reduceCtorEq]
  rw [hd]
  simp [form, hform, forwarded_dependent, hxd, forwarded_key x hxr, dependent_stripConst]
  cases env.instantiate tc x.ty.stripConst <;> rfl

/-- After the defaults, with the policy type `v`, the steps that remain
succeed exactly when `v` has the shape of an instance. -/
theorem byValue_rest (hf : f.ty.isType = true) (hx : x.ty.isType = true)
    (hfF : f.ty.formed = true) (hxF : x.ty.formed = true)
    (hfr : f.ty.isRef = false) (hxr : x.ty.isRef = false)
    (v : Ty) (hv : v.isType = true) (hvF : v.formed = true) (as : List CallArg) :
    let env := Env.ofProgram p
    let σ₁ := (2, v) :: [(1, forwarded x), (0, forwarded f)]
    (parameterListStep env (byValueObject tc).head σ₁ >>= constraintStep env (byValueObject tc).constraint
        >>= nonDependentStep env (byValueObject tc).params as >>= functionTypeStep env (byValueObject tc)) =
      if fmapShape v then .ok (byValueSpec tc f x v)
      else .soft "associated constraints not satisfied" := by
  intro env σ₁
  have h0 : Ty.subst σ₁ (.param 0) = forwarded f :=
    subst_param_type _ _ _ (by simp [σ₁, Bindings.lookup]) (forwarded_isType f hf)
  have h1 : Ty.subst σ₁ (.param 1) = forwarded x :=
    subst_param_type _ _ _ (by simp [σ₁, Bindings.lookup]) (forwarded_isType x hx)
  have h2 : Ty.subst σ₁ (.param 2) = v :=
    subst_param_type _ _ _ (by simp [σ₁, Bindings.lookup]) hv
  have hparams : formAll env [Ty.subst σ₁ (.rref (.param 0)), Ty.subst σ₁ (.rref (.param 1)),
      Ty.subst σ₁ (.param 2)] =
      .ok [Ty.collapse (.rref (forwarded f)), Ty.collapse (.rref (forwarded x)), v] := by
    show formAll env [Ty.collapse (.rref (Ty.subst σ₁ (.param 0))),
      Ty.collapse (.rref (Ty.subst σ₁ (.param 1))), Ty.subst σ₁ (.param 2)] = _
    rw [h0, h1, h2]
    simp [formAll, form_formed env _ (collapse_rref_forwarded_formed f hfF hfr),
      form_formed env _ (collapse_rref_forwarded_formed x hxF hxr), form_formed env _ hvF]
  have hplist : parameterListStep env (byValueObject tc).head σ₁ = .ok σ₁ := rfl
  have hsat : Constraint.satisfied env.atomic σ₁ (.atomic "fmap_shape" [.param 2]) =
      .ok (fmapShape v) := by
    simp only [Constraint.satisfied, List.map, h2]
    simp [env, Env.ofProgram]
  rw [hplist]
  simp only [Subst.bind_eq, Subst.bind_ok, constraintStep, byValueObject, hsat]
  cases fmapShape v
  · simp
  · have hnd : nonDependentStep env [(Ty.param 0).rref, (Ty.param 1).rref, .param 2] as σ₁ =
        .ok σ₁ := by
      rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨c, as⟩⟩⟩ <;> rfl
    simp only [↓reduceIte, Subst.pure_eq, Subst.bind_ok, hnd, functionTypeStep, List.map]
    rw [hparams]
    rfl

/-- The by-value route with the policy omitted. Deduction follows lookup
at the container's type with cv and reference removed: it succeeds when
an instance is selected, and fails hard when lookup is ambiguous. A
missing instance fails softly, but only because the primary's type,
`std::false_type`, does not have the shape the constraint checks: the
soft failure rests on the shapeless-default obligation. -/
theorem byValue_omitted_outcome (hf : f.ty.isType = true) (hx : x.ty.isType = true)
    (hfF : f.ty.formed = true) (hxF : x.ty.formed = true)
    (hfr : f.ty.isRef = false) (hxr : x.ty.isRef = false) (hxd : x.ty.dependent = false)
    (hsoft : p.any (fun | .lookup c => c = tc | _ => false) = true)
    (hhard : p.any (fun | .lookupHard c => c = tc | _ => false) = false) :
    let r := deduceTemplate (Env.ofProgram p) (byValueObject tc) [] [f, x]
    (∀ i, p.selectInstance tc x.ty.stripConst = .selected i → ∃ s, r = .ok s) ∧
    (p.selectInstance tc x.ty.stripConst = .noMatch → ∃ e, r = .soft e) ∧
    (∀ l, p.selectInstance tc x.ty.stripConst = .ambiguous l → ∃ e, r = .hard e) := by
  intro r
  have hr : r = ((Env.ofProgram p).instantiate tc x.ty.stripConst).bind fun v =>
      (parameterListStep (Env.ofProgram p) (byValueObject tc).head
          ((2, if v.dependent then .typeOf v else v.typeOfValue) :: [(1, forwarded x), (0, forwarded f)])
        >>= constraintStep (Env.ofProgram p) (byValueObject tc).constraint
        >>= nonDependentStep (Env.ofProgram p) (byValueObject tc).params [f, x]
        >>= functionTypeStep (Env.ofProgram p) (byValueObject tc)) := by
    simp only [r, deduceTemplate]
    rw [byValue_call_omitted tc f x hf hx]
    simp only [Subst.bind_eq, Subst.bind_ok]
    rw [byValue_defaults tc f x _ hx hxF hxr hxd]
    cases (Env.ofProgram p).instantiate tc x.ty.stripConst <;> rfl
  have hinst : (Env.ofProgram p).instantiate tc x.ty.stripConst =
      match p.selectInstance tc x.ty.stripConst with
      | .selected i => .ok (.spec' "instance_of" [x.ty.stripConst, .value (.int i)])
      | .ambiguous _ => .hard s!"ambiguous partial specializations of {tc}<{repr x.ty.stripConst}>"
      | .illFormed r => .hard r
      | .noMatch => .ok (.named "std::false_type") := by
    simp only [Env.ofProgram, hsoft, hhard]
    split <;> simp
  have hkF := formed_stripConst _ hxF
  have hkd : x.ty.stripConst.dependent = false := by rw [dependent_stripConst]; exact hxd
  refine ⟨fun i hi => ?_, fun hn => ?_, fun l hl => ?_⟩
  · let v : Ty := .spec' "instance_of" [x.ty.stripConst, .value (.int i)]
    have hvd : v.dependent = false := by
      simp [v, Ty.spec', Ty.args, Ty.dependent, hkd, Val.dependent]
    have hvF : v.formed = true := by
      simp [v, Ty.spec', Ty.args, Ty.formed, hkF]
    have hs := byValue_rest p tc f x hf hx hfF hxF hfr hxr v rfl hvF [f, x]
    refine ⟨byValueSpec tc f x v, ?_⟩
    rw [hr, hinst, hi]
    simp only [Subst.bind_eq, Subst.bind_ok]
    simp only [Subst.bind_eq] at hs
    rw [show (if v.dependent = true then Ty.typeOf v else v.typeOfValue) = v by
      simp only [hvd, Bool.false_eq_true, ↓reduceIte]; rfl]
    rw [hs]
    simp [fmapShape, instanceShape, v, Ty.spec']
  · have hs := byValue_rest p tc f x hf hx hfF hxF hfr hxr (.named "std::false_type") rfl rfl [f, x]
    refine ⟨"associated constraints not satisfied", ?_⟩
    rw [hr, hinst, hn]
    simp only [Subst.bind_eq, Subst.bind_ok]
    simp only [Subst.bind_eq] at hs
    exact hs
  · refine ⟨s!"ambiguous partial specializations of {tc}<{repr x.ty.stripConst}>", ?_⟩
    rw [hr, hinst, hl]
    rfl

theorem byValue_call_passed (hf : f.ty.isType = true) (hx : x.ty.isType = true) (pol : CallArg)
    (hk : pol.ty.stripConst.isType = true) :
    (explicitStep (byValueObject tc).head [] >>= callStep (byValueObject tc).params [f, x, pol]) =
      .ok [(2, pol.ty.stripConst), (1, forwarded x), (0, forwarded f)] := by
  have h0 : Ty.collapse (.rref (.param 0)) = .rref (.param 0) := rfl
  have h1 : Ty.collapse (.rref (.param 1)) = .rref (.param 1) := rfl
  have hl : ∀ t : Ty, (Ty.lref t).isType = true := fun _ => rfl
  have h2 : (Ty.param 2).stripConst = .param 2 := rfl
  cases hlf : f.lvalue <;> cases hlx : x.lvalue <;>
    simp [h0, h1, h2, hl, byValueObject, explicitStep, explicitStep.go, callStep, deduceCall,
      deduceParam, adjustP, adjustA, isForwardingRef, Ty.isRef, Ty.referred, Ty.dependent, Ty.subst,
      Bindings.lookup, deduceTy, bindArg, forwarded, hlf, hlx, hf, hx, hk]

/-- The by-value route with the policy passed. The policy type is deduced
from the argument and the default is never substituted, so the outcome
does not mention the program's instances: it is the same with none, with
an ambiguous pair, or with any other. The call is viable exactly when the
policy has the shape of an instance. -/
theorem byValue_passed (hf : f.ty.isType = true) (hx : x.ty.isType = true)
    (hfF : f.ty.formed = true) (hxF : x.ty.formed = true)
    (hfr : f.ty.isRef = false) (hxr : x.ty.isRef = false) (pol : CallArg)
    (hk : pol.ty.stripConst.isType = true) (hkF : pol.ty.stripConst.formed = true) :
    deduceTemplate (Env.ofProgram p) (byValueObject tc) [] [f, x, pol] =
      if fmapShape pol.ty.stripConst then .ok (byValueSpec tc f x pol.ty.stripConst)
      else .soft "associated constraints not satisfied" := by
  have hdef : defaultsStep (Env.ofProgram p) (byValueObject tc).head
      [(2, pol.ty.stripConst), (1, forwarded x), (0, forwarded f)] =
      .ok [(2, pol.ty.stripConst), (1, forwarded x), (0, forwarded f)] := by
    simp [defaultsStep, defaultsStep.go, Bindings.lookup, byValueObject]
  have hs := byValue_rest p tc f x hf hx hfF hxF hfr hxr pol.ty.stripConst hk hkF [f, x, pol]
  simp only [Subst.bind_eq] at hs
  simp only [deduceTemplate]
  rw [byValue_call_passed tc f x hf hx pol hk]
  simp only [Subst.bind_eq, Subst.bind_ok]
  rw [hdef, Subst.bind_ok]
  exact hs

end byValue

/-! ## The plan's routes, as an alternative design

The plan proposed three explicit-instance routes as overloads beside the
canonical one, which beman.transpose does not have
(`decisions.md#explicit-instance-routes`). They are given here so the
guidance can compare them with the library: the instance as a constant
template argument by value, as a type template argument, and as a
trailing function argument with no default. Each is constrained by the
shape of the instance's type, and none consults the lookup. The explicit
instance comes first in the two template-parameter routes, since
explicit template arguments bind the leading parameters. -/

/-- `template <auto TC, class F, class T> requires
fmap_shape<std::remove_cvref_t<decltype(TC)>> void fmap(F &&, T &&)`. -/
def valueRoute : FunctionTemplate :=
  { name := "fmap"
    head := [ { kind := .const (.named "auto") }, { kind := .type }, { kind := .type } ]
    params := [.rref (.param 1), .rref (.param 2)]
    constraint := some (.atomic "fmap_shape" [.typeOf (.value (.param 0))]) }

/-- `template <class TC, class F, class T> requires fmap_shape<TC> void
fmap(F &&, T &&)`. -/
def typeRoute : FunctionTemplate :=
  { name := "fmap"
    head := [ { kind := .type }, { kind := .type }, { kind := .type } ]
    params := [.rref (.param 1), .rref (.param 2)]
    constraint := some (.atomic "fmap_shape" [.param 0]) }

/-- `template <class F, class T, class P> requires fmap_shape<P> void
fmap(F &&, T &&, P)`: the by-value route with the policy required. With
a default it would be viable for every call the canonical overload is,
and the two would not be ordered (`routes_argument_default_ambiguous`). -/
def argumentRoute : FunctionTemplate :=
  { name := "fmap"
    head := [ { kind := .type }, { kind := .type }, { kind := .type } ]
    params := [.rref (.param 0), .rref (.param 1), .param 2]
    constraint := some (.atomic "fmap_shape" [.param 2]) }

end Overload
