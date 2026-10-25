-- Overload/DependentCandidate.lean                                   -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Units
import Overload.Members

/-!
# Dependent calls, and the fourth verdict

A call written in a template whose arguments depend on a template
parameter is a dependent call ([temp.dep.general]/2). Its name is looked
up in two contexts: unqualified lookup and argument-dependent lookup from
where the call appears in the template's definition
([temp.res.general]/1), and argument-dependent lookup again from each
point of the instantiation context ([basic.lookup.argdep]/4), which for
a function template specialization includes the end of the translation
unit ([temp.point]/7, [module.context]/5). The model's `Decl.dependentCall`
is such a call: its position is the definition context, the unit's end
the instantiation context, and its arguments are those of the
instantiation.

If the call would be ill-formed, or would find a better match, had its
lookup considered every external-linkage function declaration in its
associated namespaces in every translation unit, the program is
ill-formed, no diagnostic required ([temp.dep.candidate]/1). That is the
fourth verdict, `IllFormedNdr.dependentCandidate`, beside the three of
phase 8: the model compares what the call resolves to over the two
contexts' declarations with what it resolves to over those and every
other unit's associated-namespace functions, and reports a difference.

The theorems: for one unit there is no such verdict
(`dependentVerdicts_single`); a callee that unqualified lookup binds to
anything but a function cannot get the verdict in any program, since
argument-dependent lookup never applies to it
(`object_design_no_adl_verdict`), which is the operation object's case;
a better overload in an associated namespace of another unit is the
verdict (`late_adl_overload_verdict`); and the example of
[temp.res.general]/1, a dependent `f(t)` with `t` of a type declared
after the template, finds `f(E)` at the instantiation context
(`temp_res_general_1_example`).
-/

namespace Overload

/-! ## The lookup of a dependent call -/

/-- The points of instantiation of the specialization that the dependent
call at `pos` is instantiated for: the point immediately following each
namespace-scope declaration that refers to it, and the end of the unit,
which is a point of instantiation for every such specialization as well.
Each point once. -/
@[std rule "temp.point#1.sentence-2" "temp.point#7.sentence-1"]
def Program.instantiationPoints (p : Program) (pos : Nat) : List Nat :=
  ((p.zipIdx.filterMap fun (d, j) => if d = .refersTo pos then some (j + 1) else none)
    ++ [p.length]).eraseDups

/-- The point of instantiation of the specialization: the first of its
points. With no declaration referring to it, the unit's end. -/
def Program.instantiationPoint (p : Program) (pos : Nat) : Nat :=
  (p.instantiationPoints pos).headD p.length

/-- The lookup of a dependent call's name from its definition context and
from a point of instantiation: unqualified lookup and argument-dependent
lookup when it applies from where the call appears, and
argument-dependent lookup from the point as well. -/
@[std rule "basic.lookup.argdep#4.sentence-3"]
def Program.dependentLookupAt (p : Program) (pos point : Nat) (s : Scope) (callee : String)
    (args : List CallArg) : List Decl :=
  let u := unqualifiedLookup p pos s callee
  let d := p.callLookup pos s callee args
  if adlApplies u then d ++ (p.adl point callee args).filter (!d.contains ·) else d

/-- The lookup of a dependent call's name: during the instantiation of
the specialization the instantiation context contains its point of
instantiation. -/
@[std rule "module.context#5"]
def Program.dependentLookup (p : Program) (pos : Nat) (s : Scope) (callee : String)
    (args : List CallArg) : List Decl :=
  p.dependentLookupAt pos (p.instantiationPoint pos) s callee args

/-- The candidates of a dependent call: what its lookup found, classified
as a call's is. The name is looked up from where it appears in the
template's definition. -/
@[std rule "temp.res.general#1.sentence-1"]
def Program.dependentCandidates (p : Program) (pos : Nat) (s : Scope) (callee : String)
    (args : List CallArg) : Resolution (List Decl × List CallArg) :=
  p.candidatesOf pos (p.dependentLookup pos s callee args) callee args

/-- A dependent call, resolved over its candidates as `Program.call`
does. -/
def Program.dependentCallAt (p : Program) (env : Env) (pos : Nat) (s : Scope) (callee : String)
    (args : List CallArg) : Resolution Candidate :=
  match p.dependentCandidates pos s callee args with
  | .selected (fs, as) => p.call env fs as
  | .illFormed e => .illFormed e
  | .noMatch => .noMatch
  | .ambiguous _ => .illFormed s!"the lookup of {callee} is ambiguous"

/-! ## The verdict -/

/-- The declaration a resolution selected, by its index in the list it
resolved over, so that resolutions over different lists compare. -/
def selectionOf (decls : List Decl) (r : Resolution Candidate) : Resolution Decl :=
  r.map fun c => decls.getD c.index default

/-- What a call resolves to over a set of declarations found for its
name: the declaration selected, or the failure. -/
def Program.outcomeOver (p : Program) (env : Env) (pos : Nat) (found : List Decl) (callee : String)
    (args : List CallArg) : Resolution Decl :=
  match p.candidatesOf pos found callee args with
  | .selected (fs, as) => selectionOf fs (p.call env fs as)
  | .illFormed e => .illFormed e
  | .noMatch => .noMatch
  | .ambiguous _ => .illFormed s!"the lookup of {callee} is ambiguous"

/-- The function declarations of every other unit that argument-dependent
lookup for the call would find there. -/
def Units.othersAdl (us : Units) (u : Nat) (callee : String) (args : List CallArg) : List Decl :=
  (us.zipIdx.filter fun (_, v) => v != u).flatMap fun (q, _) => q.adl q.length callee args

/-- The verdict at a dependent call, the `pos`th declaration of unit `u`:
the call resolves differently over the declarations its two contexts
find and over those with every other unit's associated-namespace
functions as well. A call whose unqualified lookup stops
argument-dependent lookup considers no such function either way. A call
ill-formed in its own contexts is ill-formed with a diagnostic, and the
verdict adds nothing to that. -/
@[std rule "temp.dep.candidate#1"]
def dependentVerdict (us : Units) (u pos : Nat) (p : Program) (s : Scope) (callee : String)
    (args : List CallArg) : Option IllFormedNdr :=
  let env := Env.ofProgram p
  let contexts := p.dependentLookup pos s callee args
  let full :=
    if adlApplies (unqualifiedLookup p pos s callee) then
      contexts ++ (us.othersAdl u callee args).filter (!contexts.contains ·)
    else contexts
  if p.outcomeOver env pos contexts callee args != p.outcomeOver env pos full callee args then
    some (.dependentCandidate u pos callee args)
  else none

/-- Every verdict of [temp.dep.candidate]/1 about the program, at its
dependent calls. -/
def Units.dependentVerdicts (us : Units) : List IllFormedNdr :=
  us.zipIdx.flatMap fun (p, u) =>
    p.zipIdx.filterMap fun (d, pos) =>
      match d with
      | .dependentCall callee args s => dependentVerdict us u pos p s callee args
      | _ => none

/-- The verdict of [temp.point]/7 at a dependent call, the `pos`th
declaration of unit `u`: the call resolves differently at two of its
points of instantiation, so two points give the specialization different
meanings. -/
@[std rule "temp.point#7.sentence-4"]
def pointVerdict (u pos : Nat) (p : Program) (s : Scope) (callee : String)
    (args : List CallArg) : Option IllFormedNdr :=
  let env := Env.ofProgram p
  let outcome (point : Nat) :=
    p.outcomeOver env pos (p.dependentLookupAt pos point s callee args) callee args
  let first := outcome (p.instantiationPoint pos)
  if (p.instantiationPoints pos).all (fun point => outcome point == first) then none
  else some (.laterCandidate u pos callee args)

/-- Every verdict of [temp.point]/7 about the program's dependent calls. -/
def Units.pointVerdicts (us : Units) : List IllFormedNdr :=
  us.zipIdx.flatMap fun (p, u) =>
    p.zipIdx.filterMap fun (d, pos) =>
      match d with
      | .dependentCall callee args s => pointVerdict u pos p s callee args
      | _ => none

/-- Every verdict about the program: the three of phase 8 and the two of
the dependent calls. -/
def Units.allVerdicts (us : Units) : List IllFormedNdr :=
  us.verdicts ++ us.dependentVerdicts ++ us.pointVerdicts

/-! ## When the verdict cannot arise -/

/-- One unit has no other unit, so the two resolutions compare the same
declarations. -/
theorem dependentVerdict_single (p : Program) (pos : Nat) (s : Scope) (callee : String)
    (args : List CallArg) : dependentVerdict [p] 0 pos p s callee args = none := by
  have hothers : Units.othersAdl [p] 0 callee args = [] := by
    simp [Units.othersAdl, List.zipIdx]
  simp [dependentVerdict, hothers]

/-- For one unit, no dependent call gets the verdict. -/
theorem dependentVerdicts_single (p : Program) : Units.dependentVerdicts [p] = [] := by
  simp only [Units.dependentVerdicts, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.filterMap_eq_nil_iff]
  intro x hx
  obtain ⟨d, pos⟩ := x
  cases d with
  | dependentCall callee args s => exact dependentVerdict_single p pos s callee args
  | _ => rfl

/-- A callee that unqualified lookup binds to anything but a function,
an object for one, cannot get the verdict in any program: argument-
dependent lookup never applies to it, so no unit's functions enter. -/
theorem object_design_no_adl_verdict (us : Units) (u pos : Nat) (p : Program) (s : Scope)
    (callee : String) (args : List CallArg)
    (h : ∃ d ∈ unqualifiedLookup p pos s callee, d.declaresFunction = false) :
    dependentVerdict us u pos p s callee args = none := by
  have hno : adlApplies (unqualifiedLookup p pos s callee) = false := by
    obtain ⟨d, hd, hf⟩ := h
    simp only [adlApplies, List.all_eq_false]
    exact ⟨d, hd, by simp [hf]⟩
  simp [dependentVerdict, hno]

/-! ## One meaning at every point -/

/-- With no declaration referring to the call's specialization, its one
point of instantiation is the unit's end, which is how every program
without a referring declaration has been read. -/
theorem instantiationPoints_unreferenced (p : Program) (pos : Nat)
    (h : ∀ d ∈ p, d ≠ .refersTo pos) : p.instantiationPoints pos = [p.length] := by
  have hnone : p.zipIdx.filterMap
      (fun (x : Decl × Nat) => if x.1 = .refersTo pos then some (x.2 + 1) else none) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro x hx
    obtain ⟨d, j⟩ := x
    have hd : d ∈ p := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hx)
    simp [h d hd]
  simp only [Program.instantiationPoints, hnone, List.nil_append]
  rfl

/-- One point, one meaning: a call with no referring declaration gets no
verdict of [temp.point]/7. -/
theorem pointVerdict_unreferenced (u pos : Nat) (p : Program) (s : Scope) (callee : String)
    (args : List CallArg) (h : ∀ d ∈ p, d ≠ .refersTo pos) :
    pointVerdict u pos p s callee args = none := by
  simp [pointVerdict, Program.instantiationPoint, instantiationPoints_unreferenced p pos h]

/-- A callee that unqualified lookup binds to anything but a function has
one meaning at every point of instantiation: argument-dependent lookup
never applies to it, so no point adds a declaration. The operation
object's case again. -/
theorem object_design_one_meaning (u pos : Nat) (p : Program) (s : Scope) (callee : String)
    (args : List CallArg)
    (h : ∃ d ∈ unqualifiedLookup p pos s callee, d.declaresFunction = false) :
    pointVerdict u pos p s callee args = none := by
  have hno : adlApplies (unqualifiedLookup p pos s callee) = false := by
    obtain ⟨d, hd, hf⟩ := h
    simp only [adlApplies, List.all_eq_false]
    exact ⟨d, hd, by simp [hf]⟩
  simp [pointVerdict, Program.dependentLookupAt, hno]

/-! ## On programs -/

private def N : Scope := [.namespace "N"]
private def x : CallArg := { ty := .named "X", lvalue := true }

/-- A unit that defines a template calling `f(x)` with `x` an `N::X`,
derived from `N::B`, with `void f(B);` in `N`. -/
def unitWithBaseOverload : Program :=
  [ .class "B" [] [] N, .class "X" [.named "B"] [] N, .function "f" [.named "B"] N
  , .dependentCall "f" [x] ]

/-- Another unit that declares `void f(X);` in `N`, the exact match. -/
def unitWithExactOverload : Program :=
  [ .class "B" [] [] N, .class "X" [.named "B"] [] N, .function "f" [.named "X"] N ]

/-- Alone, the first unit's call selects `f(B)` through the derived-to-base
conversion and gets no verdict. With the second unit in the program, the
lookup would have found the better match `f(X)` in `N`, which neither
context sees: ill-formed, no diagnostic required. -/
theorem late_adl_overload_verdict :
    Units.dependentVerdicts [unitWithBaseOverload] = [] ∧
      (unitWithBaseOverload.dependentCallAt (Env.ofProgram unitWithBaseOverload) 3 [] "f" [x]).map
        (·.index) = .selected 0 ∧
      Units.dependentVerdicts [unitWithBaseOverload, unitWithExactOverload] =
        [.dependentCandidate 0 3 "f" [x]] := by
  refine ⟨dependentVerdicts_single _, by decide, by decide⟩

/-- `void f(char); template <class T> void g(T t) { f(t); } struct E {};
void f(E);`, the example of [temp.res.general]/1 with `E` a class rather
than an enumeration: the dependent call `f(t)` instantiated at `E`. -/
def resGeneral1Program : Program :=
  [ .function "f" [.named "char"], .dependentCall "f" [{ ty := .named "E" }]
  , .class "E", .function "f" [.named "E"], .refersTo 1 ]

/-- The same declarations with `h`, which refers to `g<E>`, before
`void f(E);`: `void f(char); template <class T> void g(T t) { f(t); }
struct E {}; void h() { g(E{}); } void f(E);`. -/
def referenceBeforeOverload : Program :=
  [ .function "f" [.named "char"], .dependentCall "f" [{ ty := .named "E" }]
  , .class "E", .refersTo 1, .function "f" [.named "E"] ]

/-- Instantiated at `E`, the call finds `f(E)` through the instantiation
context, though only `f(char)` was declared where the template is
defined, and selects it; instantiated at `char` it selects `f(char)`.
The referring declaration is the last, so the specialization has one
point of instantiation, the unit's end. One unit, so no verdict. -/
@[std example "temp.res.general#1"]
theorem temp_res_general_1_example :
    resGeneral1Program.dependentCandidates 1 [] "f" [{ ty := .named "E" }] =
        .selected ([.function "f" [.named "char"], .function "f" [.named "E"]], [{ ty := .named "E" }]) ∧
      (resGeneral1Program.dependentCallAt (Env.ofProgram resGeneral1Program) 1 [] "f"
          [{ ty := .named "E" }]).map (·.index) = .selected 1 ∧
      (resGeneral1Program.dependentCallAt (Env.ofProgram resGeneral1Program) 1 [] "f"
          [{ ty := .named "char" }]).map (·.index) = .selected 0 ∧
      resGeneral1Program.instantiationPoints 1 = [5] ∧
      Units.allVerdicts [resGeneral1Program] = [] := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- Referenced before `f(E)` is declared, the specialization has two
points of instantiation, after `h` and at the unit's end, and the call
means different things at them: at the first only `f(char)` is found,
which is not viable for an `E`, and at the end `f(E)` is selected. Two
points with different meanings is the verdict of [temp.point]/7. -/
theorem later_function_verdict :
    referenceBeforeOverload.instantiationPoints 1 = [4, 5] ∧
      (referenceBeforeOverload.dependentCallAt (Env.ofProgram referenceBeforeOverload) 1 [] "f"
          [{ ty := .named "E" }]).map (·.index) = .noMatch ∧
      referenceBeforeOverload.outcomeOver (Env.ofProgram referenceBeforeOverload) 1
          (referenceBeforeOverload.dependentLookupAt 1 5 [] "f" [{ ty := .named "E" }]) "f"
          [{ ty := .named "E" }] = .selected (.function "f" [.named "E"]) ∧
      Units.allVerdicts [referenceBeforeOverload] = [.laterCandidate 0 1 "f" [{ ty := .named "E" }]] := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end Overload
