-- Overload/Emit.lean                                                 -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Program
import Overload.Deduction

/-!
# The C++ emitter

Executable means testable: the executable side drives a generator that
emits C++ for the differential tests, and `scripts/differential.sh`
compiles each emitted program with every compiler.

A case is a program, a query, and the outcome the model expects. The
emitted translation unit checks the outcome with `static_assert`, in
unevaluated contexts only, so that no argument is ever constructed:

* a deduction case declares the function template with a return type that
  carries the deduced arguments, `deduced<T0, value_of<N1>>`, and asserts
  `decltype(f(std::declval<A>()...))` is the expected one, or that the call
  is not well-formed when deduction is expected to fail;
* a call case declares each candidate with a distinct return type
  `selected<k>` and asserts which one the call has, or that the call is
  not well-formed.

Each file states in its first line whether the model expects it to be
well-formed. A compiler that disagrees is a finding, filed against the
sentence the case cites.
-/

namespace Overload.Emit

open _root_.Overload.Std (Citation)

/-- What a case asks. -/
inductive Query where
  /-- Deduce the parameters of the function template named `callee` from
  the arguments; `expected` is the bindings, or `none` for failure. -/
  | deduction (callee : String) (args : List CallArg) (expected : Option Bindings)
  /-- Resolve a call of `callee`; `expected` names the candidate by its
  index among the candidates with that name. -/
  | call (callee : String) (args : List CallArg) (expected : Resolution Nat)
  deriving Repr, Inhabited

/-- One differential test. -/
structure Case where
  /-- The file name, without extension. -/
  name : String
  /-- The sentence the case tests. -/
  cite : Citation
  /-- The declarations. -/
  program : Program
  query : Query
  /-- Where the expectation comes from: computed by the model, or stated
  by hand from the draft's example until the model computes it. -/
  source : String := "stated"
  deriving Repr, Inhabited

/-- Is the whole translation unit expected to be well-formed? -/
def Case.wellFormed (c : Case) : Bool :=
  match c.query with
  | .deduction .. => true
  | .call _ _ (.illFormed _) => false
  | .call .. => true

/-! ## Rendering -/

private def paramName (i : ParamIdx) : String := s!"T{i}"

/-- A value as a C++ constant expression. -/
partial def val : Val → String
  | .int n => toString n
  | .bool true => "true"
  | .bool false => "false"
  | .obj c vs => s!"{c}\{{val vs}}"
  | .nil => ""
  | .cons v vs =>
    match vs with
    | .nil => val v
    | _ => s!"{val v}, {val vs}"
  | .param i => paramName i

/-- A type as C++. -/
partial def ty : Ty → String
  | .named n => n
  | .param i => paramName i
  | .const t => s!"const {ty t}"
  | .ptr t => s!"{ty t}*"
  | .lref t => s!"{ty t}&"
  | .rref t => s!"{ty t}&&"
  | .spec c as => s!"{c}<{argList as}>"
  | .nil => ""
  | .cons a as => argList (.cons a as)
  | .value v => val v
  | .nondeduced t => s!"std::type_identity_t<{ty t}>"
where
  argList (as : Ty) : String :=
    match as.toList with
    | some l => String.intercalate ", " (l.map ty)
    | none => ty as

/-- A template head as C++. -/
def head (h : Head) : String :=
  let ps := h.zipIdx.map fun (p, i) =>
    let decl := match p.kind with
      | .type => s!"class {paramName i}"
      | .const t => s!"{ty t} {paramName i}"
    match p.default with
    | some d => s!"{decl} = {ty d}"
    | none => decl
  s!"template <{String.intercalate ", " ps}>"

/-- The parameters of a function as C++. -/
def params (ps : List Ty) : String :=
  String.intercalate ", " (ps.map ty)

/-- The argument expressions of a call, all unevaluated. -/
def args (as : List CallArg) : String :=
  String.intercalate ", " <| as.map fun a =>
    if a.lvalue then s!"std::declval<{ty a.ty}&>()" else s!"std::declval<{ty a.ty}>()"

/-- The argument types of a call as template arguments of `viable`, an
lvalue as `T&` and an rvalue as `T`, so that `static_cast<A&&>` inside the
requires-expression yields the same value categories as `args`. -/
def argTypes (as : List CallArg) : String :=
  String.intercalate ", " <| as.map fun a =>
    if a.lvalue then s!"{ty a.ty}&" else ty a.ty

/-- The assertion that a call is not viable. The requires-expression must
be dependent: outside a template, a call with no matching function is an
error rather than a false requires-expression. -/
def notViable (callee : String) (as : List CallArg) : String :=
  s!"template <class... A>\nconstexpr bool viable = requires(A&&... a) \{ {callee}(static_cast<A&&>(a)...); };\n" ++
    s!"static_assert(!viable<{argTypes as}>);\n"

/-- The return type that carries deduced arguments. -/
def deducedType (h : Head) : String :=
  let parts := h.zipIdx.map fun (p, i) =>
    match p.kind with
    | .type => paramName i
    | .const _ => s!"value_of<{paramName i}>"
  s!"deduced<{String.intercalate ", " parts}>"

/-- The expected `deduced<...>` for a set of bindings. -/
def expectedDeduced (h : Head) (σ : Bindings) : String :=
  let parts := h.zipIdx.map fun (_, i) =>
    match σ.lookup i with
    | some (.value v) => s!"value_of<{val v}>"
    | some t => ty t
    | none => "void"
  s!"deduced<{String.intercalate ", " parts}>"

/-- The declarations of a program, as C++; functions named `callee` get
the return type `ret k` for the `k`th candidate. -/
def program (p : Program) (callee : String) (ret : Nat → Head → String) : String := Id.run do
  let mut out := ""
  let mut k := 0
  for d in p do
    match d with
    | .class n [] => out := out ++ s!"struct {n} \{};\n"
    | .class n bases =>
      out := out ++ s!"struct {n} : {String.intercalate ", " (bases.map (s!"public {·}"))} \{};\n"
    | .classTemplate n h => out := out ++ s!"{head h}\nstruct {n} \{};\n"
    | .function n ps =>
      if n = callee then
        out := out ++ s!"{ret k []} {n}({params ps});\n"
        k := k + 1
      else
        out := out ++ s!"void {n}({params ps});\n"
    | .functionTemplate n h ps =>
      if n = callee then
        out := out ++ s!"{head h}\n{ret k h} {n}({params ps});\n"
        k := k + 1
      else
        out := out ++ s!"{head h}\nvoid {n}({params ps});\n"
    | .lookup c =>
      out := out ++ s!"template <class T>\ninline constexpr auto {c} = std::false_type\{};\n"
    | .instance c h pat =>
      out := out ++ s!"{head h}\ninline constexpr auto {c}<{ty pat}> = instance_of<{ty pat}>\{};\n"
    | .use c t =>
      out := out ++ s!"static_assert(sizeof({c}<{ty t}>) > 0);\n"
  return out

/-- The whole translation unit for a case. -/
def render (c : Case) : String := Id.run do
  let mut out := ""
  out := out ++ s!"// expect: {if c.wellFormed then "well-formed" else "ill-formed"}\n"
  out := out ++ s!"// case: {c.name}\n"
  out := out ++ s!"// cites: {c.cite} <{c.cite.url}>\n"
  out := out ++ s!"// expectation: {c.source}\n"
  out := out ++ "// Generated by `lake exe emit`; do not edit.\n"
  out := out ++ "#include <type_traits>\n#include <utility>\n\n"
  out := out ++ "template <class...> struct deduced {};\n"
  out := out ++ "template <auto V> struct value_of {};\n"
  out := out ++ "template <int K> struct selected {};\n"
  out := out ++ "template <class T> struct instance_of {};\n\n"
  match c.query with
  | .deduction callee as expected =>
    let p := c.program
    let h := match p.candidates callee with
      | .functionTemplate _ h _ :: _ => h
      | _ => []
    out := out ++ program p callee (fun _ h => deducedType h) ++ "\n"
    match expected with
    | some σ =>
      out := out ++ s!"static_assert(std::is_same_v<decltype({callee}({args as})), {expectedDeduced h σ}>);\n"
    | none =>
      out := out ++ notViable callee as
  | .call callee as expected =>
    out := out ++ program c.program callee (fun k _ => s!"selected<{k}>") ++ "\n"
    match expected with
    | .selected k =>
      out := out ++ s!"static_assert(std::is_same_v<decltype({callee}({args as})), selected<{k}>>);\n"
    | .noMatch | .ambiguous _ =>
      out := out ++ notViable callee as
    | .illFormed r =>
      out := out ++ s!"// the model expects a hard error: {r}\n"
      out := out ++ s!"using probe = decltype({callee}({args as}));\n"
  return out

/-! ## The cases -/

/-- A citation, for the case list. -/
private def cite (s : String) : Citation :=
  match Std.parseCitation s with
  | .ok c => c
  | .error _ => default

/-- The draft's example in [temp.deduct.call]/3: `template<class T> int
f(const T&); f(5)` calls `f<int>`. -/
def draftDeductCall3_rvalue : Case :=
  { name := "draft_temp_deduct_call_3_rvalue"
    cite := cite "temp.deduct.call#3"
    program := [.functionTemplate "f" [{ kind := .type }] [.lref (.const (.param 0))]]
    query := .deduction "f" [{ ty := .named "int" }] (some [(0, .named "int")])
    source := "computed by deduceCall" }

/-- The same template with a `const int` lvalue: still `f<int>`. -/
def draftDeductCall3_lvalue : Case :=
  { name := "draft_temp_deduct_call_3_lvalue"
    cite := cite "temp.deduct.call#3"
    program := [.functionTemplate "f" [{ kind := .type }] [.lref (.const (.param 0))]]
    query := .deduction "f" [{ ty := .const (.named "int"), lvalue := true }] (some [(0, .named "int")])
    source := "computed by deduceCall" }

/-- A forwarding reference with an lvalue argument deduces an lvalue
reference. -/
def forwardingLvalue : Case :=
  { name := "temp_deduct_call_3_forwarding_lvalue"
    cite := cite "temp.deduct.call#3.sentence-4"
    program := [.functionTemplate "f" [{ kind := .type }] [.rref (.param 0)]]
    query := .deduction "f" [{ ty := .named "int", lvalue := true }] (some [(0, .lref (.named "int"))])
    source := "computed by deduceCall" }

/-- A forwarding reference with an rvalue argument deduces the type. -/
def forwardingRvalue : Case :=
  { name := "temp_deduct_call_3_forwarding_rvalue"
    cite := cite "temp.deduct.call#3.sentence-4"
    program := [.functionTemplate "f" [{ kind := .type }] [.rref (.param 0)]]
    query := .deduction "f" [{ ty := .named "int" }] (some [(0, .named "int")])
    source := "computed by deduceCall" }

/-- The form `TT<T>`: deduction through a class template specialization. -/
def specialization : Case :=
  { name := "temp_deduct_type_8_specialization"
    cite := cite "temp.deduct.type#8"
    program :=
      [ .classTemplate "box" [{ kind := .type }]
      , .functionTemplate "f" [{ kind := .type }] [.spec' "box" [.param 0]] ]
    query := .deduction "f" [{ ty := .spec' "box" [.named "int"] }] (some [(0, .named "int")])
    source := "computed by deduceCall" }

/-- The form `T*` against a non-pointer: deduction fails. -/
def pointerMismatch : Case :=
  { name := "temp_deduct_type_8_pointer_mismatch"
    cite := cite "temp.deduct.type#8"
    program := [.functionTemplate "f" [{ kind := .type }] [.ptr (.param 0)]]
    query := .deduction "f" [{ ty := .named "int" }] none
    source := "computed by deduceCall" }

/-- Two parameters deducing the same template parameter must agree. -/
def inconsistent : Case :=
  { name := "temp_deduct_type_2_inconsistent"
    cite := cite "temp.deduct.type#2.sentence-3"
    program := [.functionTemplate "f" [{ kind := .type }] [.param 0, .param 0]]
    query := .deduction "f" [{ ty := .named "int" }, { ty := .named "long" }] none
    source := "computed by deduceCall" }

/-- A non-template is preferred over a template specialization when the
conversion sequences are indistinguishable. Stated until phase 5. -/
def nonTemplatePreferred : Case :=
  { name := "over_match_best_general_2_non_template"
    cite := cite "over.match.best.general#2"
    program :=
      [ .functionTemplate "f" [{ kind := .type }] [.param 0]
      , .function "f" [.named "int"] ]
    query := .call "f" [{ ty := .named "int" }] (.selected 1) }

/-- Every case the emitter writes. -/
def cases : List Case :=
  [ draftDeductCall3_rvalue, draftDeductCall3_lvalue, forwardingLvalue, forwardingRvalue
  , specialization, pointerMismatch, inconsistent, nonTemplatePreferred ]

/-- For a deduction case, what the model computes, so that the stated
expectation and the computed one can be compared in the tests. -/
def computed (c : Case) : Option (Option Bindings) :=
  match c.query with
  | .deduction callee as _ =>
    match c.program.candidates callee with
    | .functionTemplate _ h ps :: _ =>
      some <| (deduceCall ps as []).bind fun σ => if allDeduced h.length σ then some σ else none
    | _ => none
  | .call .. => none

end Overload.Emit
