-- Overload/Units.lean                                                -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Environment
import Overload.Resolution

/-!
# Translation units, and what cannot be said about them

A program is a list of translation units, each resolved on its own. The
model gives no meaning to a program in which one entity has two contrary
definitions. It reports that the program is ill-formed with no diagnostic
required, names the rule and the use, and says nothing more
(`decisions.md#single-tu`).

The verdicts are about variable template lookup. A use of a lookup,
`tc<a>`, selects among the partial specializations it can reach. The
selection must be the one it would make with every partial specialization
of the program reachable:

* one declared later in the same unit gives the specialization a second
  point of instantiation, at the end of the unit, with a different
  meaning ([temp.point]/7);
* one declared only in another unit is not reachable from a use that
  would make use of it ([temp.spec.partial.general]/1);
* where the use is a test of a registry for completeness, a specialization
  that changes the test's answer makes one satisfaction result differ at
  two points ([temp.constr.atomic]/3).

For one unit, the standing assumption of `single-tu` is exactly what
rules every verdict out (`verdicts_single`, `registry_verdicts_single`).
Per unit, a call sees only the declarations before it, so a partial
specialization declared after a use leaves the use as it was and either
leaves the program free of a verdict or gives it the verdict of
[temp.point]/7 (`callAt_insert_after`, `late_insertion_verdict`). What the
typeclass encoding makes of this, divergence between units and stability
of a call per unit, is in `Overload/Typeclass/Units.lean`.
-/

namespace Overload

open PartialOrdering

/-- A program of several translation units. -/
abbrev Units := List Program

/-- The instances of `tc` that a list of declarations makes reachable,
each partial specialization once: when the primary template's name is
used, the reachable partial specializations are considered. -/
@[std rule "temp.spec.partial.general#7"]
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
  /-- A use that tests a registry for completeness, `requires { R<a>{}; }`,
  answers differently from the answer it would give with every
  specialization reachable: one satisfaction result at two points (the
  registry section below). -/
  | satisfactionChanged (unit pos : Nat) (registry : String) (arg : Ty)
  /-- A dependent call would be ill-formed, or would find a better match,
  had its lookup considered every external-linkage function declaration
  in its associated namespaces in every unit, not only those of its
  definition and instantiation contexts (`Overload/DependentCandidate.lean`). -/
  | dependentCandidate (unit pos : Nat) (callee : String) (args : List CallArg)
  /-- A variable template specialization instantiated in two units that
  define it differently: its initializer selects different partial
  specializations in the two, so the definitions of one definable item
  do not agree. -/
  | odrMismatch (unit other : Nat) (tc : String) (arg : Ty)
  deriving Repr, DecidableEq

attribute [std rule "temp.point#7"] IllFormedNdr.laterInUnit
attribute [std rule "temp.spec.partial.general#1.sentence-3"] IllFormedNdr.notReachable
attribute [std rule "temp.constr.atomic#3.sentence-5"] IllFormedNdr.satisfactionChanged
attribute [std rule "temp.dep.candidate#1"] IllFormedNdr.dependentCandidate
attribute [std rule "basic.def.odr#16"] IllFormedNdr.odrMismatch

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
  [ .classTemplate "box" [{ kind := .type }], .lookup "trait"
  , .instance "trait" [{ kind := .type }] (box T), .use "trait" (box int) ]

/-- A unit that uses the lookup at `box<int>` without the instance. -/
def unitWithoutInstance : Program :=
  [ .classTemplate "box" [{ kind := .type }], .lookup "trait", .use "trait" (box int) ]

/-- A unit that declares the instance after its use. -/
def unitLateInstance : Program :=
  [ .classTemplate "box" [{ kind := .type }], .lookup "trait", .use "trait" (box int)
  , .instance "trait" [{ kind := .type }] (box T) ]

/-- Each unit alone is a well-formed program; together they are
ill-formed with no diagnostic required, at the use of the unit without
the instance. -/
theorem missing_instance_verdict :
    Units.verdicts [unitWithoutInstance] = [] ∧ Units.verdicts [unitWithInstance] = [] ∧
      Units.verdicts [unitWithInstance, unitWithoutInstance] = [.notReachable 1 2 "trait" (box int)] := by
  refine ⟨rfl, rfl, rfl⟩

/-- An instance declared after a use gives the lookup a second point of
instantiation with a different meaning. -/
theorem late_instance_verdict :
    Units.verdicts [unitLateInstance] = [.laterInUnit 0 2 "trait" (box int)] := rfl


/-! ## Stability, per unit -/

/-- A call as the declarations of its unit before it see it: the call is
at position `pos`, and only what precedes it is reachable. `envOf` is how
a program becomes an environment, `Env.ofProgram` or a layer's extension
of it. -/
def callAt (envOf : Program → Env) (p : Program) (pos : Nat) (r : Ranking Conv) (decls : List Decl)
    (args : List CallArg) : Resolution Candidate :=
  resolve .text (envOf (p.take pos)) r decls args

theorem take_insert_after (p : Program) (j pos : Nat) (inst : Decl) (hj : j ≤ p.length)
    (hpos : pos < j) : (p.take j ++ inst :: p.drop j).take pos = p.take pos := by
  have hl : pos ≤ (p.take j).length := by simp; omega
  rw [List.take_append_of_le_length hl, List.take_take, Nat.min_eq_left (by omega)]

/-- An instance declared after a call leaves the call as it was. -/
theorem callAt_insert_after (envOf : Program → Env) (p : Program) (j pos : Nat) (inst : Decl)
    (r : Ranking Conv) (decls : List Decl) (args : List CallArg) (hj : j ≤ p.length) (hpos : pos < j) :
    callAt envOf (p.take j ++ inst :: p.drop j) pos r decls args = callAt envOf p pos r decls args := by
  unfold callAt
  rw [take_insert_after p j pos inst hj hpos]

/-- An instance declared before a call, as `call_stability` sees it: the
call's prefix gains the instance. -/
theorem take_insert_before (p : Program) (j pos : Nat) (inst : Decl) (hj : j ≤ pos)
    (hpos : pos ≤ p.length) :
    (p.take j ++ inst :: p.drop j).take (pos + 1) = p.take j ++ inst :: (p.drop j).take (pos - j) ∧
      p.take pos = p.take j ++ (p.drop j).take (pos - j) := by
  have hl : (p.take j).length = j := by simp; omega
  constructor
  · rw [List.take_append, hl, List.take_of_length_le (by omega),
      show pos + 1 - j = (pos - j) + 1 by omega, List.take_succ_cons]
  · conv => lhs; rw [← List.take_append_drop j p]
    rw [List.take_append, hl, List.take_of_length_le (by omega)]

/-- An instance declared after a use of the lookup leaves what the use
selects as it was. The program stays free of a verdict at the use when
the whole unit selects the same, and otherwise gets the verdict of
[temp.point]/7, and nothing else: it is the end of the unit that sees
the instance. -/
theorem late_insertion_verdict (p : Program) (j pos : Nat) (tc c : String) (h : Head) (pat a : Ty)
    (hj : j ≤ p.length) (hpos : pos < j) :
    let p' := p.take j ++ .instance c h pat :: p.drop j
    let before := selection (reachable (p.take pos) tc) tc a
    (useVerdict [p'] 0 pos p' tc a = none ∧ before = selection (reachable p' tc) tc a) ∨
      (useVerdict [p'] 0 pos p' tc a = some (.laterInUnit 0 pos tc a) ∧
        before ≠ selection (reachable p' tc) tc a) := by
  intro p' before
  have hprog : Units.instancesOf [p'] tc = reachable p' tc := by simp [Units.instancesOf, reachable]
  have ht : p'.take pos = p.take pos := take_insert_after p j pos _ hj hpos
  unfold useVerdict
  rw [hprog, ht]
  dsimp only
  by_cases he : before = selection (reachable p' tc) tc a
  · left
    have he' := he
    simp only [before] at he
    exact ⟨by simp [he], he'⟩
  · right
    have he' := he
    simp only [before] at he
    exact ⟨by simp [he], he'⟩


/-! ## A registry tested by completeness

A registry is a class template declared and never defined, `Registry<V>`.
An entry is a specialization of it, explicit or partial, and a use tests
for one by completeness, `requires { Registry<V>{}; }`. In the model a
registry's specializations are `Decl.instance` declarations and a test is
a `Decl.use`, so its selection is computed as a lookup's is. Its test
answers whether that selection finds a specialization. beman.transpose's
`Monoid` is one (`Overload/Typeclass/Members.lean`). -/

/-- What a completeness test answers, given the specializations it can
reach: whether one matches. -/
def completeAt (insts : List (Head × Ty)) (registry : String) (a : Ty) : Bool :=
  (selection insts registry a).toOption.isSome

/-- Where a verdict is: its unit, the position of the use, the name and the
argument. -/
def IllFormedNdr.site : IllFormedNdr → Nat × Nat × String × Ty
  | .laterInUnit u pos tc a | .notReachable u pos tc a | .satisfactionChanged u pos tc a => (u, pos, tc, a)
  | .dependentCandidate u pos callee args => (u, pos, callee, Ty.args (args.map (·.ty)))
  | .odrMismatch u v tc a => (u, v, tc, a)

/-- The rule a verdict at a registry's use falls under. Where the test's
answer itself changes, from incomplete to complete, the use is one
satisfaction result at two points ([temp.constr.atomic]/3). Where only the
specialization selected changes, it is the rule the lookup's verdict
already names. -/
def registryCite (us : Units) (registries : List String) : IllFormedNdr → IllFormedNdr
  | .laterInUnit u pos tc a =>
    let p := us.getD u []
    if tc ∈ registries ∧
        completeAt (reachable (p.take pos) tc) tc a ≠ completeAt (reachable p tc) tc a then
      .satisfactionChanged u pos tc a
    else .laterInUnit u pos tc a
  | .notReachable u pos tc a =>
    let p := us.getD u []
    if tc ∈ registries ∧
        completeAt (reachable (p.take pos) tc) tc a ≠ completeAt (us.instancesOf tc) tc a then
      .satisfactionChanged u pos tc a
    else .notReachable u pos tc a
  | v => v

/-- The verdicts of a program in which the uses of `registries` are
completeness tests. -/
def Units.registryVerdicts (us : Units) (registries : List String) : List IllFormedNdr :=
  us.verdicts.map (registryCite us registries)

theorem registryCite_site (us : Units) (registries : List String) (v : IllFormedNdr) :
    (registryCite us registries v).site = v.site := by
  cases v <;> simp only [registryCite] <;> split <;> rfl

/-- A completeness registry has exactly the verdicts of a lookup: at the
same uses, of the same name and argument. Only the rule may differ, where
the test's answer changes. -/
theorem registry_verdicts (us : Units) (registries : List String) :
    (us.registryVerdicts registries).map IllFormedNdr.site = us.verdicts.map IllFormedNdr.site := by
  simp only [Units.registryVerdicts, List.map_map]
  congr 1
  funext v
  exact registryCite_site us registries v

/-- For one unit, every specialization before every test is again exactly
what keeps the program free of a verdict. -/
theorem registry_verdicts_single (p : Program) (h : SingleTranslationUnit p) (registries : List String) :
    Units.registryVerdicts [p] registries = [] := by
  simp [Units.registryVerdicts, verdicts_single p h]

/-- A registry tested at `std::string`, then specialized for it: the test
answered incomplete, and with the specialization reachable it answers
complete. -/
def registryLate : Program :=
  [ .use "Registry" (.named "std::string"), .instance "Registry" [] (.named "std::string") ]

theorem registry_late_verdict :
    Units.registryVerdicts [registryLate] ["Registry"] = [.satisfactionChanged 0 0 "Registry" (.named "std::string")] ∧
    Units.verdicts [registryLate] = [.laterInUnit 0 0 "Registry" (.named "std::string")] := by
  decide

/-! ## One definable item, two definitions

A variable template specialization `tc<a>` is a definable item, defined
in every unit that instantiates it. Its definitions must agree, names
denoting the same entity after lookup, which for the specialization
means the same partial specialization selected ([basic.def.odr]/16). Two
units whose lookups select differently define it differently. That
verdict never comes first: one of the two selections differs from what
the whole program would select, which is already the verdict of
[temp.point]/7 or [temp.spec.partial.general]/1 at that unit's use
(`odr_verdict_implies_verdict`). The encoding's
`operation_object_not_separated` is this situation for the operation
object (`Overload/Typeclass/Units.lean`). -/

/-- The variable template specializations a unit instantiates. -/
def Program.usesOf (p : Program) : List (String × Ty) :=
  p.filterMap fun
    | .use tc a => some (tc, a)
    | _ => none

/-- The verdicts of [basic.def.odr]/16 at the lookups: two units that both
instantiate `tc<a>` and select different partial specializations. -/
@[std rule "basic.def.odr#16"]
def Units.odrVerdicts (us : Units) : List IllFormedNdr :=
  us.zipIdx.flatMap fun (p, u) =>
    us.zipIdx.flatMap fun (q, v) =>
      if u < v then
        (p.usesOf.filter (q.usesOf.contains ·)).filterMap fun (tc, a) =>
          if selection (reachable p tc) tc a != selection (reachable q tc) tc a then
            some (.odrMismatch u v tc a)
          else none
      else []

theorem usesOf_mem (p : Program) (tc : String) (a : Ty) (h : (tc, a) ∈ p.usesOf) :
    ∃ pos : Nat, p[pos]? = some (Decl.use tc a) := by
  simp only [Program.usesOf, List.mem_filterMap] at h
  obtain ⟨d, hd, hval⟩ := h
  cases d <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hval
  obtain ⟨rfl, rfl⟩ := hval
  exact List.mem_iff_getElem?.1 hd

/-- A use whose unit selects differently from the whole program gets a
verdict of phase 8 at that use. -/
theorem use_verdict_of_ne (us : Units) (u pos : Nat) (p : Program) (tc : String) (a : Ty)
    (hp : us[u]? = some p) (hpos : p[pos]? = some (.use tc a))
    (hne : selection (reachable p tc) tc a ≠ selection (us.instancesOf tc) tc a) :
    ∃ w ∈ us.verdicts, w.site = (u, pos, tc, a) := by
  have hv : ∃ w, useVerdict us u pos p tc a = some w ∧ w.site = (u, pos, tc, a) := by
    unfold useVerdict
    by_cases h1 : selection (reachable (p.take pos) tc) tc a = selection (reachable p tc) tc a
    · rw [h1]
      have h2 : (selection (reachable p tc) tc a != selection (us.instancesOf tc) tc a) = true := by
        simpa [bne_iff_ne] using hne
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, h2]
      exact ⟨_, rfl, rfl⟩
    · have h2 : (selection (reachable (p.take pos) tc) tc a != selection (reachable p tc) tc a) = true := by
        simpa [bne_iff_ne] using h1
      simp only [h2, ↓reduceIte]
      exact ⟨_, rfl, rfl⟩
  obtain ⟨w, hw, hsite⟩ := hv
  refine ⟨w, ?_, hsite⟩
  simp only [Units.verdicts, List.mem_flatMap, List.mem_filterMap]
  refine ⟨(p, u), List.mem_zipIdx_iff_getElem?.2 hp, (.use tc a, pos),
    List.mem_zipIdx_iff_getElem?.2 hpos, ?_⟩
  simpa using hw

/-- The verdict of [basic.def.odr]/16 never comes first: a program with
one has a verdict of phase 8 already. -/
theorem odr_verdict_implies_verdict (us : Units) (h : us.odrVerdicts ≠ []) : us.verdicts ≠ [] := by
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ h
  simp only [Units.odrVerdicts, List.mem_flatMap] at hw
  obtain ⟨⟨p, u⟩, hp, ⟨q, v⟩, hq, hw⟩ := hw
  split at hw
  · simp only [List.mem_filterMap, List.mem_filter] at hw
    obtain ⟨⟨tc, a⟩, ⟨hpu, hqu⟩, hsel⟩ := hw
    split at hsel
    · next hne =>
      rw [bne_iff_ne] at hne
      have hp' : us[u]? = some p := by simpa using List.mem_zipIdx_iff_getElem?.1 hp
      have hq' : us[v]? = some q := by simpa using List.mem_zipIdx_iff_getElem?.1 hq
      obtain ⟨pos, hpos⟩ := usesOf_mem p tc a hpu
      obtain ⟨posq, hposq⟩ := usesOf_mem q tc a (by simpa using hqu)
      by_cases hall : selection (reachable p tc) tc a = selection (us.instancesOf tc) tc a
      · have hne' : selection (reachable q tc) tc a ≠ selection (us.instancesOf tc) tc a := by
          rw [← hall]; exact fun e => hne e.symm
        obtain ⟨w', hw', _⟩ := use_verdict_of_ne us v posq q tc a hq' hposq hne'
        exact List.ne_nil_of_mem hw'
      · obtain ⟨w', hw', _⟩ := use_verdict_of_ne us u pos p tc a hp' hpos hall
        exact List.ne_nil_of_mem hw'
    · cases hsel
  · simp at hw

/-- A unit that declares an instance for `box<int>` alone, and uses the
lookup there. -/
def unitWithExactInstance : Program :=
  [ .classTemplate "box" [{ kind := .type }], .lookup "trait"
  , .instance "trait" [] (box int), .use "trait" (box int) ]

/-- Two units whose lookups at `box<int>` select different partial
specializations define `trait<box<int>>` differently; and the program
already has a verdict of phase 8, at the use of the unit that cannot
reach the more specialized instance the whole program would select. -/
theorem odr_mismatch_example :
    Units.odrVerdicts [unitWithInstance, unitWithExactInstance] =
        [.odrMismatch 0 1 "trait" (box int)] ∧
      Units.verdicts [unitWithInstance, unitWithExactInstance] =
        [.notReachable 0 3 "trait" (box int)] := by
  refine ⟨by decide, by decide⟩

end Overload
