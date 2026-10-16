-- Overload/Emit.lean                                                 -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Program
import Overload.Deduction
import Overload.Steps
import Overload.Resolution

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
  is not viable when deduction is expected to fail;
* a call case declares each candidate with a distinct return type
  `selected<k>` and asserts which one the call has, that the call is not
  viable, or, for an expected hard error, names the call's type so the
  translation unit is ill-formed;
* a raw case is C++ written by hand, for the draft's examples that use
  more of the language than the model has, with the assertion included.

Each file states in its first line whether the model expects it to be
well-formed. A compiler that disagrees is a finding, filed against the
sentence the case cites.
-/

namespace Overload.Emit

open _root_.Overload.Std (Citation)

/-- What a case asks. -/
inductive Query where
  /-- Deduce the parameters of the function template named `callee` from
  the explicit template arguments and the call's arguments; `expected` is
  the bindings, or `none` for a deduction failure. -/
  | deduction (callee : String) (args : List CallArg) (expected : Option Bindings)
      (explicit : List Ty := [])
  /-- Resolve a call of `callee`; `expected` names the candidate by its
  index among the candidates with that name. -/
  | call (callee : String) (args : List CallArg) (expected : Resolution Nat)
  /-- Hand-written C++ with its own assertions, and whether it is
  well-formed. -/
  | raw (cpp : String) (wellFormed : Bool := true)
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
  | .raw _ wf => wf

/-! ## The environment a program defines -/

/-- Does an instance of `tc` in the program match the type `a`? Phase 4
replaces first-match with partial specialization matching and ordering. -/
def instanceMatches (p : Program) (tc : String) (a : Ty) : Bool :=
  p.any fun
    | .instance c h pat =>
      c = tc && (match deduceTy pat a [] with
        | some σ => allDeduced h.length σ
        | none => false)
    | _ => false

/-- The environment a program defines: the lookups it declares, hard or
soft, with their instances; `has_instance` as the one atomic constraint;
and convertibility as identity up to top-level cv and references. -/
def Env.ofProgram (p : Program) : Env :=
  { instantiate := fun n a =>
      let hard := p.any fun | .lookupHard c => c = n | _ => false
      let soft := p.any fun | .lookup c => c = n | _ => false
      if instanceMatches p n a then .ok (.spec' "instance_of" [a])
      else if hard then .hard s!"static_assert in the primary {n}<{repr a}>"
      else if soft then .ok (.named "std::false_type")
      else .soft s!"no variable template {n}"
    atomic := fun e args =>
      match e, args with
      | "has_instance", [.named c, a] => .ok (instanceMatches p c a)
      | _, _ => .soft s!"unknown atomic constraint {e}"
    convertible := fun a t => .ok (a.ty.referred.stripConst == t.referred.stripConst) }

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
  | .lookup n a => s!"{n}<{ty a}>"
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

/-- A constraint as a requires-clause. `has_instance` is spelled out as
the encoding spells it; any other atomic constraint is a concept-id. -/
def constraint : Constraint → String
  | .atomic "has_instance" [.named c, a] =>
    s!"(!std::is_same_v<std::remove_cvref_t<decltype({c}<{ty a}>)>, std::false_type>)"
  | .atomic e m => s!"{e}<{String.intercalate ", " (m.map ty)}>"
  | .conj l r => s!"({constraint l} && {constraint r})"
  | .disj l r => s!"({constraint l} || {constraint r})"

/-- The parameters of a function as C++, the last `defaults` of them with
a default argument. -/
def params (ps : List Ty) (defaults : Nat := 0) : String :=
  let n := ps.length
  String.intercalate ", " <| ps.zipIdx.map fun (p, i) =>
    if i + defaults ≥ n then s!"{ty p} = \{}" else ty p

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

/-- A call expression, with explicit template arguments if any. -/
def callExpr (callee : String) (explicit : List Ty) (as : List CallArg) : String :=
  let name := if explicit.isEmpty then callee
    else s!"{callee}<{String.intercalate ", " (explicit.map ty)}>"
  s!"{name}({args as})"

/-- The assertion that a call is not viable. The requires-expression must
be dependent: outside a template, a call with no matching function is an
error rather than a false requires-expression. -/
def notViable (callee : String) (explicit : List Ty) (as : List CallArg) : String :=
  let name := if explicit.isEmpty then callee
    else s!"{callee}<{String.intercalate ", " (explicit.map ty)}>"
  s!"template <class... A>\nconstexpr bool viable = requires(A&&... a) \{ {name}(static_cast<A&&>(a)...); };\n" ++
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
    | .functionTemplate ft =>
      let req := match ft.constraint with
        | some c => s!"\n    requires {constraint c}"
        | none => ""
      if ft.name = callee then
        out := out ++ s!"{head ft.head}{req}\n{ret k ft.head} {ft.name}({params ft.params ft.defaultArgs});\n"
        k := k + 1
      else
        out := out ++ s!"{head ft.head}{req}\nvoid {ft.name}({params ft.params ft.defaultArgs});\n"
    | .lookup c =>
      out := out ++ s!"template <class T>\ninline constexpr auto {c} = std::false_type\{};\n"
    | .lookupHard c =>
      out := out ++ s!"template <class T>\nstruct {c}_instance \{\n"
      out := out ++ s!"    static_assert(sizeof(T) == 0, \"no {c} instance for this type\");\n"
      out := out ++ s!"    static constexpr int value = 0;\n};\n"
      out := out ++ s!"template <class T>\ninline constexpr auto {c} = {c}_instance<T>::value;\n"
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
  | .deduction callee as expected explicit =>
    let p := c.program
    let h := (p.functionTemplate? callee).map (·.head) |>.getD []
    out := out ++ program p callee (fun _ h => deducedType h) ++ "\n"
    match expected with
    | some σ =>
      out := out ++ s!"static_assert(std::is_same_v<decltype({callExpr callee explicit as}), {expectedDeduced h σ}>);\n"
    | none =>
      out := out ++ notViable callee explicit as
  | .call callee as expected =>
    out := out ++ program c.program callee (fun k _ => s!"selected<{k}>") ++ "\n"
    match expected with
    | .selected k =>
      out := out ++ s!"static_assert(std::is_same_v<decltype({callExpr callee [] as}), selected<{k}>>);\n"
    | .noMatch | .ambiguous _ =>
      out := out ++ notViable callee [] as
    | .illFormed r =>
      out := out ++ s!"// the model expects a hard error: {r}\n"
      out := out ++ s!"using probe = decltype({callExpr callee [] as});\n"
  | .raw cpp _ =>
    out := out ++ program c.program "" (fun _ _ => "void") ++ "\n" ++ cpp
  return out

/-! ## The cases -/

/-- A citation, for the case list. -/
private def cite (s : String) : Citation :=
  match Std.parseCitation s with
  | .ok c => c
  | .error _ => default

private def T : Ty := .param 0
private def U : Ty := .param 1
private def int : Ty := .named "int"
private def typeParam : TemplateParam := { kind := .type }

/-- `template <class T> ... f(params)` with no defaults or constraints. -/
private def simpleTemplate (ps : List Ty) : Decl :=
  .functionTemplate { name := "f", head := [typeParam], params := ps }

/-- The draft's example in [temp.deduct.call]/3: `template<class T> int
f(const T&); f(5)` calls `f<int>`. -/
def draftDeductCall3_rvalue : Case :=
  { name := "draft_temp_deduct_call_3_rvalue"
    cite := cite "temp.deduct.call#3"
    program := [simpleTemplate [.lref (.const T)]]
    query := .deduction "f" [{ ty := int }] (some [(0, int)])
    source := "computed by deduceTemplate" }

/-- The same template with a `const int` lvalue: still `f<int>`. -/
def draftDeductCall3_lvalue : Case :=
  { name := "draft_temp_deduct_call_3_lvalue"
    cite := cite "temp.deduct.call#3"
    program := [simpleTemplate [.lref (.const T)]]
    query := .deduction "f" [{ ty := .const int, lvalue := true }] (some [(0, int)])
    source := "computed by deduceTemplate" }

/-- A forwarding reference with an lvalue argument deduces an lvalue
reference. -/
def forwardingLvalue : Case :=
  { name := "temp_deduct_call_3_forwarding_lvalue"
    cite := cite "temp.deduct.call#3.sentence-4"
    program := [simpleTemplate [.rref T]]
    query := .deduction "f" [{ ty := int, lvalue := true }] (some [(0, .lref int)])
    source := "computed by deduceTemplate" }

/-- A forwarding reference with an rvalue argument deduces the type. -/
def forwardingRvalue : Case :=
  { name := "temp_deduct_call_3_forwarding_rvalue"
    cite := cite "temp.deduct.call#3.sentence-4"
    program := [simpleTemplate [.rref T]]
    query := .deduction "f" [{ ty := int }] (some [(0, int)])
    source := "computed by deduceTemplate" }

/-- The form `TT<T>`: deduction through a class template specialization. -/
def specialization : Case :=
  { name := "temp_deduct_type_8_specialization"
    cite := cite "temp.deduct.type#8"
    program := [.classTemplate "box" [typeParam], simpleTemplate [.spec' "box" [T]]]
    query := .deduction "f" [{ ty := .spec' "box" [int] }] (some [(0, int)])
    source := "computed by deduceTemplate" }

/-- The form `T*` against a non-pointer: deduction fails. -/
def pointerMismatch : Case :=
  { name := "temp_deduct_type_8_pointer_mismatch"
    cite := cite "temp.deduct.type#8"
    program := [simpleTemplate [.ptr T]]
    query := .deduction "f" [{ ty := int }] none
    source := "computed by deduceTemplate" }

/-- Two parameters deducing the same template parameter must agree. -/
def inconsistent : Case :=
  { name := "temp_deduct_type_2_inconsistent"
    cite := cite "temp.deduct.type#2.sentence-3"
    program := [simpleTemplate [T, T]]
    query := .deduction "f" [{ ty := int }, { ty := .named "long" }] none
    source := "computed by deduceTemplate" }

/-- A non-template is preferred over a template specialization when the
conversion sequences are indistinguishable. Stated until phase 5. -/
def nonTemplatePreferred : Case :=
  { name := "over_match_best_general_2_non_template"
    cite := cite "over.match.best.general#2"
    program := [simpleTemplate [T], .function "f" [int]]
    query := .call "f" [{ ty := int }] (.selected 1)
    source := "computed by resolve" }

/-! ### [temp.deduct.general]/5, the first example

`template <class T, class U = double> void f(T t = 0, U u = 0);` -/

private def defaultedTemplate : Decl :=
  .functionTemplate
    { name := "f"
      head := [typeParam, { kind := .type, default := some (.named "double") }]
      params := [T, U]
      defaultArgs := 2 }

/-- `f(1, 'c')` is `f<int,char>(1,'c')`. -/
def draftDeductGeneral5_both : Case :=
  { name := "draft_temp_deduct_general_5_both"
    cite := cite "temp.deduct.general#5.sentence-2"
    program := [defaultedTemplate]
    query := .deduction "f" [{ ty := int }, { ty := .named "char" }]
      (some [(0, int), (1, .named "char")])
    source := "computed by deduceTemplate" }

/-- `f(1)` is `f<int,double>(1,0)`: `U` takes its default. -/
def draftDeductGeneral5_default : Case :=
  { name := "draft_temp_deduct_general_5_default"
    cite := cite "temp.deduct.general#5.sentence-2"
    program := [defaultedTemplate]
    query := .deduction "f" [{ ty := int }] (some [(0, int), (1, .named "double")])
    source := "computed by deduceTemplate" }

/-- `f()` is an error: `T` cannot be deduced. -/
def draftDeductGeneral5_undeduced : Case :=
  { name := "draft_temp_deduct_general_5_undeduced"
    cite := cite "temp.deduct.type#4.sentence-4"
    program := [defaultedTemplate]
    query := .deduction "f" [] none
    source := "computed by deduceTemplate" }

/-- `f<int>()` is `f<int,double>(0,0)`. -/
def draftDeductGeneral5_explicit : Case :=
  { name := "draft_temp_deduct_general_5_explicit"
    cite := cite "temp.deduct.general#2.sentence-2"
    program := [defaultedTemplate]
    query := .deduction "f" [] (some [(0, int), (1, .named "double")]) (explicit := [int])
    source := "computed by deduceTemplate" }

/-- `f<int,char>()` is `f<int,char>(0,0)`. -/
def draftDeductGeneral5_explicitBoth : Case :=
  { name := "draft_temp_deduct_general_5_explicit_both"
    cite := cite "temp.deduct.general#2.sentence-2"
    program := [defaultedTemplate]
    query := .deduction "f" [] (some [(0, int), (1, .named "char")])
      (explicit := [int, .named "char"])
    source := "computed by deduceTemplate" }

/-! ### [temp.deduct.general]/5, the second example

Constraints are checked before the function type is substituted, and
non-dependent parameters before that: both calls select #2 and neither
reaches the return type of #1, which would be a hard error for `int`. -/

def draftDeductGeneral5_stepOrder : Case :=
  { name := "draft_temp_deduct_general_5_step_order"
    cite := cite "temp.deduct.general#5.sentence-6"
    program := []
    query := .raw "template <class T> struct Z {
  typedef typename T::x xx;
};
template <class T> concept C = requires { typename T::A; };
template <C T> typename Z<T>::xx f(void *, T);          // #1
template <class T> selected<2> f(int, T);               // #2
struct A {} a;
struct ZZ {
  template <class T, class = typename Z<T>::xx> operator T *();
  operator int();
};
ZZ zz;
// OK, deduction fails for #1 because there is no conversion from int to void*
static_assert(std::is_same_v<decltype(f(1, a)), selected<2>>);
// OK, deduction fails for #1 because C<int> is not satisfied
static_assert(std::is_same_v<decltype(f(zz, 42)), selected<2>>);
"
    source := "the draft's example; the Lean reproduction is in OverloadTest/Steps.lean" }

/-! ### [temp.deduct.general]/8, the example

Forming "pointer to reference to int" fails in #1's function type, in the
immediate context, so the call selects #2. -/

def draftDeductGeneral8_immediate : Case :=
  { name := "draft_temp_deduct_general_8_immediate_context"
    cite := cite "temp.deduct.general#8.sentence-3"
    program := []
    query := .raw "template<typename T>
T* fun(T&& v);  // #1: the deduction substitution locus is the function type
selected<2> fun(...);  // #2
int i;
static_assert(std::is_same_v<decltype(fun(i)), selected<2>>);
"
    source := "the draft's example; the Lean reproduction is in OverloadTest/Steps.lean" }

/-! ### The step-order hazard

The plan's suspect, in the model: a defaulted constant template parameter
whose default performs a lookup that fails hard poisons the call, even
though the non-template candidate is the exact match. The soft design,
with `std::false_type` as the default instance and the candidate
constrained on finding one, selects the non-template. -/

private def hazardTemplate (constrained : Bool) : FunctionTemplate :=
  { name := "f"
    head :=
      [ typeParam
      , { kind := .const (.lref (.const (.named "auto")))
          default := some (.lookup "functor" T) } ]
    params := [T, int]
    constraint := if constrained then some (.atomic "has_instance" [.named "functor", T]) else none }

/-- Variant A of the step-order probe: the hard design. Clang follows the
text and rejects the program; GCC compiles it under the P3606 shortcut, a
known disagreement (docs/findings.md). -/
def stepOrderHazard : Case :=
  { name := "step_order_hazard"
    cite := cite "temp.deduct.general#5.sentence-3"
    program :=
      [ .class "X", .lookupHard "functor"
      , .functionTemplate (hazardTemplate false)
      , .function "f" [.named "X", int] ]
    query := .call "f" [{ ty := .named "X" }, { ty := int }]
      (.illFormed "the default of T1 instantiates functor<X>, whose primary fails")
    source := "computed by resolve under the text; well-formed under P3606" }

/-- Variant C: a requires-clause on the same template cannot guard the
default, since constraints are checked after defaults are substituted. -/
def stepOrderHazardGuarded : Case :=
  { name := "step_order_hazard_guarded"
    cite := cite "temp.deduct.general#5.sentence-6"
    program :=
      [ .class "X", .lookupHard "functor"
      , .functionTemplate (hazardTemplate true)
      , .function "f" [.named "X", int] ]
    query := .call "f" [{ ty := .named "X" }, { ty := int }]
      (.illFormed "the default of T1 instantiates functor<X> before the constraint is checked")
    source := "computed by resolve under the text; well-formed under P3606" }

/-- Variant D: the soft design selects the non-template on both compilers. -/
def stepOrderSoft : Case :=
  { name := "step_order_soft"
    cite := cite "temp.deduct.general#5.sentence-7"
    program :=
      [ .class "X", .lookup "functor"
      , .functionTemplate (hazardTemplate true)
      , .function "f" [.named "X", int] ]
    query := .call "f" [{ ty := .named "X" }, { ty := int }] (.selected 1)
    source := "computed by resolve" }

/-! ### [temp.constr.atomic]/3, the example

A hard error while checking the satisfaction of #1's constraint makes the
call ill-formed even though #2 is a better match. Under P3606, #2 is a
perfect match and #1 is never deduced. -/

def draftConstrAtomic3_betterMatch : Case :=
  { name := "draft_temp_constr_atomic_3_better_match"
    cite := cite "temp.constr.atomic#3"
    program := []
    query := .raw "template<typename T> struct S {
  constexpr operator bool() const { return true; }
};

template<typename T> requires (S<T>{})
void f(T);                      // #1
void f(int);                    // #2

// error: expression S<int>{} does not have type bool while checking
// satisfaction of deduced arguments of #1; call is ill-formed even though
// #2 is a better match
using probe = decltype(f(0));\n" (wellFormed := false)
    source := "the draft's example; the Lean reproduction is in OverloadTest/Resolution.lean" }

/-- Every case the emitter writes. -/
def cases : List Case :=
  [ draftDeductCall3_rvalue, draftDeductCall3_lvalue, forwardingLvalue, forwardingRvalue
  , specialization, pointerMismatch, inconsistent, nonTemplatePreferred
  , draftDeductGeneral5_both, draftDeductGeneral5_default, draftDeductGeneral5_undeduced
  , draftDeductGeneral5_explicit, draftDeductGeneral5_explicitBoth
  , draftDeductGeneral5_stepOrder, draftDeductGeneral8_immediate
  , stepOrderHazard, stepOrderHazardGuarded, stepOrderSoft, draftConstrAtomic3_betterMatch ]

/-- Bindings in head order, for comparison. -/
def normalize (arity : Nat) (σ : Bindings) : List (ParamIdx × Ty) :=
  (List.range arity).filterMap fun i => (σ.lookup i).map (i, ·)

/-- For a deduction case, what the model computes, so that the stated
expectation and the computed one can be compared in the tests: `some
(some σ)` for success, `some none` for a deduction failure, and `none`
when the case is not a deduction case or the outcome was a hard error. -/
def computed (c : Case) : Option (Option (List (ParamIdx × Ty))) :=
  match c.query with
  | .deduction callee as _ explicit =>
    match c.program.functionTemplate? callee with
    | some ft =>
      match deduceTemplate (Env.ofProgram c.program) ft explicit as with
      | .ok s => some (some (normalize ft.head.length s.args))
      | .soft _ => some none
      | .hard _ => none
    | none => none
  | _ => none

/-- For a call case, what the model computes under the text, as candidate
indices; `none` when the case is not a call case. -/
def computedCall (c : Case) : Option (Resolution Nat) :=
  match c.query with
  | .call callee as _ =>
    some ((resolve .text (Env.ofProgram c.program) identityRanking
      (decls := c.program.candidates callee) (args := as)).map (·.index))
  | _ => none

/-- Do two resolutions agree, ignoring the reason of an ill-formed one? -/
def Resolution.agree : Resolution Nat → Resolution Nat → Bool
  | .selected a, .selected b => a == b
  | .noMatch, .noMatch => true
  | .ambiguous a, .ambiguous b => a == b
  | .illFormed _, .illFormed _ => true
  | _, _ => false

/-- The stated expectation of a deduction case, normalized the same way. -/
def stated (c : Case) : Option (Option (List (ParamIdx × Ty))) :=
  match c.query with
  | .deduction callee _ expected _ =>
    match c.program.functionTemplate? callee with
    | some ft => some (expected.map (normalize ft.head.length))
    | none => none
  | _ => none

end Overload.Emit
