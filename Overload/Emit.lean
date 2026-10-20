-- Overload/Emit.lean                                                 -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Separability
import Overload.Erasure
import Overload.Mandates
import Overload.Sfinae
import Overload.Dispatch
import Overload.Units
import Overload.Access
import Overload.Scope

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

The cases here are the Standard side's. A case carries its own prelude,
the fixtures its program needs beyond the common ones, so a layer above
the Standard can add cases of its own with its own fixtures
(`Overload/Typeclass/Emit.lean`); `Tools/Emit.lean` emits both lists.
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
  /-- Resolve a call of `callee`, with explicit template arguments if
  any; `expected` names the candidate by its index among the candidates
  with that name. -/
  | call (callee : String) (args : List CallArg) (expected : Resolution Nat)
      (explicit : List Ty := [])
  /-- Hand-written C++ with its own assertions, and whether it is
  well-formed. -/
  | raw (cpp : String) (wellFormed : Bool := true)
  /-- Which partial specialization of the lookup variable template `name`
  the argument selects; `expected` indexes the program's partial
  specializations of it, in order, `noMatch` is the primary, and
  `ambiguous` is ill-formed. -/
  | lookup (name : String) (arg : Ty) (expected : Resolution Nat)
  deriving Repr, Inhabited

/-- The fixture every emitted unit declares: `deduced<...>` and
`value_of<V>` carry deduced arguments, `ref_of<R>` a deduced reference,
and `instance_of<T>` is the model's name for a selected specialization's
value. -/
def commonPrelude : String :=
  "template <class...> struct deduced {};\n" ++
  "template <auto V> struct value_of {};\n" ++
  "template <class T> struct instance_of {};\n" ++
  "template <const auto &R> struct ref_of {};\n"

/-- The default fixture of a case: `selected<K>` with no members. -/
def defaultPrelude : String := "template <int K> struct selected {};\n"

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
  /-- Ground truths of atomic constraints the program's concepts define,
  for the model's oracle: `(expression, arguments, holds)`. -/
  atomics : List (String × List Ty × Bool) := []
  /-- The fixtures the emitted unit declares after the common ones:
  `selected<K>`, the return type that identifies the `K`th candidate and
  the type of the `K`th partial specialization's value, and whatever else
  the case's programs name. -/
  prelude : String := defaultPrelude
  deriving Repr, Inhabited

/-- Is the whole translation unit expected to be well-formed? -/
def Case.wellFormed (c : Case) : Bool :=
  match c.query with
  | .deduction .. => true
  | .call _ _ (.illFormed _) _ => false
  | .call .. => true
  | .raw _ wf => wf
  | .lookup _ _ (.ambiguous _) | .lookup _ _ (.illFormed _) => false
  | .lookup .. => true

/-! ## The environment a program defines -/

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
  | .synth i => s!"synthesized_{i}"
  | .param i => paramName i
  | .const t => s!"const {ty t}"
  | .ptr t => s!"{ty t}*"
  | .lref t => s!"{ty t}&"
  | .rref t => s!"{ty t}&&"
  | .spec "auto" as => s!"{argList as} auto"
  | .spec c as => s!"{c}<{argList as}>"
  | .nil => ""
  | .cons a as => argList (.cons a as)
  | .value v => val v
  | .nondeduced t => s!"std::type_identity_t<{ty t}>"
  | .lookup n a => s!"{n}<{ty a}>"
  | .ref t => ty t
  | .removeCvref t => s!"std::remove_cvref_t<{ty t}>"
  | .typeOf t => s!"std::remove_cvref_t<decltype({ty t})>"
  | .enableIf c as t => s!"std::enable_if_t<{c}<{argList as}>, {ty t}>"
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

/-- A constraint as a requires-clause. `has_instance` and `lookup_formed`
are spelled out as conditions on the lookup variable; any other atomic
constraint is a concept-id, which the case's prelude or program must
declare. -/
def constraint : Constraint → String
  | .atomic "has_instance" [.named c, a] =>
    s!"(!std::is_same_v<std::remove_cvref_t<decltype({c}<{ty a}>)>, std::false_type>)"
  | .atomic "lookup_formed" [.named c, a] => s!"(sizeof(decltype({c}<{ty a}>)) > 0)"
  | .atomic e m =>
    if e.startsWith "!" then s!"(!{e.drop 1}<{String.intercalate ", " (m.map ty)}>)"
    else s!"{e}<{String.intercalate ", " (m.map ty)}>"
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
    | .const (.lref _) => s!"ref_of<{paramName i}>"
    | .const _ => s!"value_of<{paramName i}>"
  s!"deduced<{String.intercalate ", " parts}>"

/-- The expected `deduced<...>` for a set of bindings. -/
def expectedDeduced (h : Head) (σ : Bindings) : String :=
  let parts := h.zipIdx.map fun (_, i) =>
    match σ.lookup i with
    | some (.value v) => s!"value_of<{val v}>"
    | some (.ref t) => s!"ref_of<{ty t}>"
    | some t => ty t
    | none => "void"
  s!"deduced<{String.intercalate ", " parts}>"

/-- A function template's body: a declaration only, or, with Mandates, a
definition whose `static_assert` checks them when it is instantiated. -/
def body (ft : FunctionTemplate) (ret : String) : String :=
  match ft.mandate with
  | some m =>
    if ret == "void" then s!" \{ static_assert({constraint m}); }"
    else s!" \{ static_assert({constraint m}); return \{}; }"
  | none => ";"

/-- A function template's declarator, with the case's return type `r`
in place of its own. `enable_if` in the return type keeps its condition
and is spelled as a trailing return type: the model substitutes the
return type after the parameters, which is the lexical order
([temp.deduct.general]/7) of a trailing return type. -/
def declarator (ft : FunctionTemplate) (r : String) (ps : String) : String :=
  match ft.ret with
  | .enableIf c as _ => s!"auto {ft.name}({ps}) -> {ty (.enableIf c as (.named r))}"
  | _ => s!"{r} {ft.name}({ps})"

/-- Does any function template of the program have Mandates? -/
def hasMandates (p : Program) : Bool :=
  p.any fun
    | .functionTemplate ft => ft.mandate.isSome
    | _ => false

/-- An evaluated call, in a function body, so that the selected
specialization's definition is instantiated and its Mandates checked. -/
def evaluatedCall (callee : String) (explicit : List Ty) (as : List CallArg) : String :=
  let name := if explicit.isEmpty then callee
    else s!"{callee}<{String.intercalate ", " (explicit.map ty)}>"
  let ps := as.zipIdx.map fun (a, i) => if a.lvalue then s!"{ty a.ty}& a{i}" else s!"{ty a.ty}&& a{i}"
  let es := as.zipIdx.map fun (a, i) =>
    if a.lvalue then s!"a{i}" else s!"static_cast<{ty a.ty}&&>(a{i})"
  s!"void evaluated({String.intercalate ", " ps}) \{ {name}({String.intercalate ", " es}); }\n"

/-- The index of a declaration's entity among the callee's entities
declared so far, and the entities after it: a redeclaration shares its
entity's index, and gets the same return type, as C++ requires. -/
private def entityIndex (ents : List Decl) (d : Decl) : Nat × List Decl :=
  match ents.findIdx? (corresponds · d) with
  | some k => (k, ents)
  | none => (ents.length, ents ++ [d])

/-- The declarations of a program, as C++; functions named `callee` get
the return type `ret k` for the `k`th entity of that name, which is its
index in the overload set. -/
def program (p : Program) (callee : String) (ret : Nat → Head → String) : String := Id.run do
  let mut out := ""
  let mut ents : List Decl := []
  let mut instances : List (String × Nat) := []
  for d in p do
    match d with
    | .class n [] [] => out := out ++ s!"struct {n} \{};\n"
    | .class n bases prot =>
      let specs := bases.map (s!"public {ty ·}") ++ prot.map (s!"protected {ty ·}")
      out := out ++ s!"struct {n} : {String.intercalate ", " specs} \{};\n"
    | .classTemplate n h => out := out ++ s!"{head h}\nstruct {n} \{};\n"
    | .function n ps =>
      if n = callee then
        let (k, ents') := entityIndex ents d
        ents := ents'
        out := out ++ s!"{ret k []} {n}({params ps});\n"
      else
        out := out ++ s!"void {n}({params ps});\n"
    | .functionTemplate ft =>
      let req := match ft.constraint with
        | some c => s!"\n    requires {constraint c}"
        | none => ""
      if ft.name = callee then
        let (k, ents') := entityIndex ents d
        ents := ents'
        out := out ++ s!"{head ft.head}{req}\n{declarator ft (ret k ft.head) (params ft.params ft.defaultArgs)}{body ft (ret k ft.head)}\n"
      else
        out := out ++ s!"{head ft.head}{req}\n{declarator ft "void" (params ft.params ft.defaultArgs)}{body ft "void"}\n"
    | .lookup c =>
      out := out ++ s!"template <class T>\ninline constexpr auto {c} = std::false_type\{};\n"
    | .lookupHard c =>
      out := out ++ s!"template <class T>\nstruct {c}_instance \{\n"
      out := out ++ s!"    static_assert(sizeof(T) == 0, \"no {c} instance for this type\");\n"
      out := out ++ s!"    static constexpr int value = 0;\n};\n"
      out := out ++ s!"template <class T>\ninline constexpr auto {c} = {c}_instance<T>::value;\n"
    | .instance c h pat =>
      let i := (instances.find? (·.1 == c)).map (·.2) |>.getD 0
      instances := (c, i + 1) :: instances.filter (·.1 != c)
      out := out ++ s!"{head h}\ninline constexpr selected<{i}> {c}<{ty pat}>\{};\n"
    | .concept n body =>
      out := out ++ s!"template <class T>\nconcept {n} = {body};\n"
    | .use c t =>
      out := out ++ s!"static_assert(sizeof({c}<{ty t}>) > 0);\n"
    | .object n =>
      out := out ++ s!"inline constexpr pinned_instance {n}\{};\n"
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
  out := out ++ commonPrelude ++ c.prelude ++ "\n"
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
  | .call callee as expected explicit =>
    out := out ++ program c.program callee (fun k _ => s!"selected<{k}>") ++ "\n"
    match expected with
    | .selected k =>
      out := out ++ s!"static_assert(std::is_same_v<decltype({callExpr callee explicit as}), selected<{k}>>);\n"
    | .noMatch | .ambiguous _ =>
      out := out ++ notViable callee explicit as
    | .illFormed r =>
      out := out ++ s!"// the model expects a hard error: {r}\n"
      out := out ++ s!"using probe = decltype({callExpr callee explicit as});\n"
    if hasMandates c.program then
      match expected with
      | .selected _ | .illFormed _ => out := out ++ evaluatedCall callee explicit as
      | _ => pure ()
  | .raw cpp _ =>
    out := out ++ program c.program "" (fun _ _ => "void") ++ "\n" ++ cpp
  | .lookup tc a expected =>
    out := out ++ program c.program "" (fun _ _ => "void") ++ "\n"
    let value := s!"std::remove_cvref_t<decltype({tc}<{ty a}>)>"
    match expected with
    | .selected k =>
      out := out ++ s!"static_assert(std::is_same_v<{value}, selected<{k}>>);\n"
    | .noMatch =>
      out := out ++ s!"static_assert(std::is_same_v<{value}, std::false_type>);\n"
    | .ambiguous _ | .illFormed _ =>
      out := out ++ s!"// the model expects a hard error: ambiguous partial specializations\n"
      out := out ++ s!"using probe = decltype({tc}<{ty a}>);\n"
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

/-- `void f(int); void f(int); void f(char);` and `f(1)`: the second
declaration corresponds to the first and is the same function, so the
call selects it and is not ambiguous. -/
def redeclarationNotOverload : Case :=
  { name := "basic_scope_scope_4_redeclaration"
    cite := cite "basic.scope.scope#4"
    program := redeclaredProgram
    query := .call "f" [{ ty := int }] (.selected 0)
    source := "computed by resolve over the overload set" }

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
          default := some (.lookup "trait" T) } ]
    params := [T, int]
    constraint := if constrained then some (.atomic "has_instance" [.named "trait", T]) else none }

/-- Variant A of the step-order probe: the hard design. Clang follows the
text and rejects the program; GCC compiles it under the P3606 shortcut, a
known disagreement (docs/findings.md). -/
def stepOrderHazard : Case :=
  { name := "step_order_hazard"
    cite := cite "temp.deduct.general#5.sentence-3"
    program :=
      [ .class "X", .lookupHard "trait"
      , .functionTemplate (hazardTemplate false)
      , .function "f" [.named "X", int] ]
    query := .call "f" [{ ty := .named "X" }, { ty := int }]
      (.illFormed "the default of T1 instantiates trait<X>, whose primary fails")
    source := "computed by resolve under the text; well-formed under P3606" }

/-- Variant C: a requires-clause on the same template cannot guard the
default, since constraints are checked after defaults are substituted. -/
def stepOrderHazardGuarded : Case :=
  { name := "step_order_hazard_guarded"
    cite := cite "temp.deduct.general#5.sentence-6"
    program :=
      [ .class "X", .lookupHard "trait"
      , .functionTemplate (hazardTemplate true)
      , .function "f" [.named "X", int] ]
    query := .call "f" [{ ty := .named "X" }, { ty := int }]
      (.illFormed "the default of T1 instantiates trait<X> before the constraint is checked")
    source := "computed by resolve under the text; well-formed under P3606" }

/-- Variant D: the soft design selects the non-template on both compilers. -/
def stepOrderSoft : Case :=
  { name := "step_order_soft"
    cite := cite "temp.deduct.general#5.sentence-7"
    program :=
      [ .class "X", .lookup "trait"
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

/-! ### The tie-break probe

Two overloads where the second is more constrained, varying how the
instance bound is written. [temp.func.order]/8 compares constraints only
when the template parameter lists are equivalent. -/

private def c1 : Constraint := .atomic "c1" [T]
private def c2 : Constraint := .conj (.atomic "c1" [T]) (.atomic "is_empty" [T])
private def concepts : List Decl :=
  [ .concept "c1" "std::is_class_v<T>", .concept "is_empty" "std::is_empty_v<T>"
  , .concept "shape" "std::is_class_v<T>" ]
private def tieAtomics : List (String × List Ty × Bool) :=
  [("c1", [.named "X"], true), ("is_empty", [.named "X"], true), ("shape", [.named "std::false_type"], true)]

/-- Variant A: requires-clauses only; #2 is more constrained. -/
def tieBreakA : Case :=
  { name := "tie_break_requires_only"
    cite := cite "temp.func.order#8"
    program := [.class "X"] ++ concepts ++
      [ .functionTemplate { name := "g", head := [typeParam], params := [T], constraint := some c1 }
      , .functionTemplate { name := "g", head := [typeParam], params := [T], constraint := some c2 } ]
    query := .call "g" [{ ty := .named "X" }] (.selected 1)
    source := "computed by resolve"
    atomics := tieAtomics }

/-- Variant B: #2 has an extra defaulted template parameter, so the
parameter lists differ in length and the tie-break is off. -/
def tieBreakB : Case :=
  { name := "tie_break_extra_parameter"
    cite := cite "temp.func.order#8"
    program := [.class "X", .lookup "trait"] ++ concepts ++
      [ .functionTemplate { name := "g", head := [typeParam], params := [T], constraint := some c1 }
      , .functionTemplate
          { name := "g"
            head := [typeParam, { kind := .const (.named "auto"), default := some (.lookup "trait" T) }]
            params := [T], constraint := some c2 } ]
    query := .call "g" [{ ty := .named "X" }] (.ambiguous [0, 1])
    source := "computed by resolve"
    atomics := tieAtomics }

/-- Variant C: the bound is a type-constraint on an `auto` constant
parameter. [temp.over.link]/6 ignores it for equivalence, so the tie-break
applies and #2 wins. -/
def tieBreakC : Case :=
  { name := "tie_break_placeholder_constraint"
    cite := cite "temp.over.link#6"
    program := [.class "X", .lookup "trait"] ++ concepts ++
      [ .functionTemplate
          { name := "g"
            head := [typeParam, { kind := .const (.named "auto"), default := some (.lookup "trait" T) }]
            params := [T], constraint := some c1 }
      , .functionTemplate
          { name := "g"
            head := [typeParam, { kind := .const (.spec' "auto" [.named "shape"]), default := some (.lookup "trait" T) }]
            params := [T], constraint := some c2 } ]
    query := .call "g" [{ ty := .named "X" }] (.selected 1)
    source := "computed by resolve"
    atomics := tieAtomics }

/-- Variant D: constant parameters of different concrete types are not
equivalent, so the tie-break is off. -/
def tieBreakD : Case :=
  { name := "tie_break_different_types"
    cite := cite "temp.over.link#6"
    program := [.class "X"] ++ concepts ++
      [ .functionTemplate
          { name := "g"
            head := [typeParam, { kind := .const int, default := some (.value (.int 0)) }]
            params := [T], constraint := some c1 }
      , .functionTemplate
          { name := "g"
            head := [typeParam, { kind := .const (.named "long"), default := some (.value (.int 0)) }]
            params := [T], constraint := some c2 } ]
    query := .call "g" [{ ty := .named "X" }] (.ambiguous [0, 1])
    source := "computed by resolve"
    atomics := tieAtomics }

/-! ### Partial ordering of templates and of instances -/

/-- `f(T&)` is more specialized than `f(T&&)` for an lvalue: the reference
tie-break of [temp.deduct.partial]/9. -/
def refTieBreak : Case :=
  { name := "temp_deduct_partial_9_lvalue_reference"
    cite := cite "temp.deduct.partial#9"
    program := [.class "X", simpleTemplate [.lref T], simpleTemplate [.rref T]]
    query := .call "f" [{ ty := .named "X", lvalue := true }] (.selected 0)
    source := "computed by resolve" }

/-- `f(const T&)` is more specialized than `f(T&&)` for a const lvalue. -/
def cvTieBreak : Case :=
  { name := "temp_deduct_partial_9_cv_qualified"
    cite := cite "temp.deduct.partial#9"
    program := [.class "X", simpleTemplate [.lref (.const T)], simpleTemplate [.rref T]]
    query := .call "f" [{ ty := .const (.named "X"), lvalue := true }] (.selected 0)
    source := "computed by resolve" }

/-- `f(T*)` is more specialized than `f(T)`. -/
def pointerMoreSpecialized : Case :=
  { name := "temp_func_order_pointer"
    cite := cite "temp.deduct.partial#10"
    program := [.class "X", simpleTemplate [T], simpleTemplate [.ptr T]]
    query := .call "f" [{ ty := .ptr (.named "X") }] (.selected 1)
    source := "computed by resolve" }

/-- An instance for `box<int>` is more specialized than one for `box<T>`. -/
def instanceMoreSpecialized : Case :=
  { name := "temp_spec_partial_match_more_specialized"
    cite := cite "temp.spec.partial.match#1"
    program :=
      [ .classTemplate "box" [typeParam], .lookup "trait"
      , .instance "trait" [typeParam] (.spec' "box" [T])
      , .instance "trait" [] (.spec' "box" [int]) ]
    query := .lookup "trait" (.spec' "box" [int]) (.selected 1)
    source := "computed by select" }

/-- `pair<T, int>` and `pair<int, T>` both match `pair<int, int>` and
neither is more specialized: ambiguous. -/
def instanceAmbiguous : Case :=
  { name := "temp_spec_partial_match_ambiguous"
    cite := cite "temp.spec.partial.match#1"
    program :=
      [ .classTemplate "pair" [typeParam, typeParam], .lookup "trait"
      , .instance "trait" [typeParam] (.spec' "pair" [T, int])
      , .instance "trait" [typeParam] (.spec' "pair" [int, T]) ]
    query := .lookup "trait" (.spec' "pair" [int, int]) (.ambiguous [0, 1])
    source := "computed by select" }

/-- No instance matches: the primary, `std::false_type`. -/
def instancePrimary : Case :=
  { name := "temp_spec_partial_match_primary"
    cite := cite "temp.spec.partial.match#1"
    program :=
      [ .classTemplate "box" [typeParam], .lookup "trait"
      , .instance "trait" [typeParam] (.spec' "box" [T]) ]
    query := .lookup "trait" int .noMatch
    source := "computed by select" }

/-! ### Ranking conversion sequences

Computed with the program's ranking (`Program.ranking`): the identity
conversion, the derived-to-base conversion and direct reference
binding. -/

private def A : Ty := .named "A"
private def B : Ty := .named "B"
private def C : Ty := .named "C"
private def X : Ty := .named "X"
private def chain : Program := [.class "A", .class "B" [.named "A"], .class "C" [.named "B"]]

/-- `C` to `B` is better than `C` to `A`, by value: the draft's example in
[over.ics.rank]/4 without the pointers. -/
def rankDerivedToBase : Case :=
  { name := "over_ics_rank_derived_to_base"
    cite := cite "over.ics.rank#4"
    program := chain ++ [.function "f" [A], .function "f" [B]]
    query := .call "f" [{ ty := C }] (.selected 1)
    source := "computed by resolve" }

/-- Binding `B&` to an lvalue `B` is an exact match, and binding `A&` is a
derived-to-base conversion: the draft's example in [over.ics.ref]/1. -/
def rankReferenceExact : Case :=
  { name := "over_ics_ref_exact_over_derived"
    cite := cite "over.ics.ref#1"
    program := chain ++ [.function "f" [.lref A], .function "f" [.lref B]]
    query := .call "f" [{ ty := B, lvalue := true }] (.selected 1)
    source := "computed by resolve" }

/-- An rvalue reference bound to an rvalue beats an lvalue reference:
`g(const X&&)` for an rvalue. -/
def rankRvalueBinding : Case :=
  { name := "over_ics_rank_rvalue_binding"
    cite := cite "over.ics.rank#3"
    program := [.class "X", .function "g" [.lref (.const X)], .function "g" [.rref (.const X)]]
    query := .call "g" [{ ty := X }] (.selected 1)
    source := "computed by resolve" }

/-- The same pair for an lvalue: the rvalue reference cannot bind. -/
def rankLvalueBinding : Case :=
  { name := "over_ics_rank_lvalue_binding"
    cite := cite "over.ics.ref#3.sentence-1"
    program := [.class "X", .function "g" [.lref (.const X)], .function "g" [.rref (.const X)]]
    query := .call "g" [{ ty := X, lvalue := true }] (.selected 0)
    source := "computed by resolve" }

/-- `f(X&)` beats `f(const X&)` for a non-const lvalue: the less
qualified reference wins. -/
def rankQualification : Case :=
  { name := "over_ics_rank_qualification"
    cite := cite "over.ics.rank#3"
    program := [.class "X", .function "f" [.lref (.const X)], .function "f" [.lref X]]
    query := .call "f" [{ ty := X, lvalue := true }] (.selected 1)
    source := "computed by resolve" }

/-- `g(const X&)` and `g(X)` are indistinguishable for an lvalue: the
draft's `int k = g(i); // ambiguous`. -/
def rankValueReferenceAmbiguous : Case :=
  { name := "over_ics_rank_value_reference_ambiguous"
    cite := cite "over.ics.rank#3"
    program := [.class "X", .function "g" [.lref (.const X)], .function "g" [X]]
    query := .call "g" [{ ty := X, lvalue := true }] (.ambiguous [0, 1])
    source := "computed by resolve" }

private def rank0 : Ty := .named "rank0"
private def rank1 : Ty := .named "rank1"
private def rank2 : Ty := .named "rank2"
private def tags : Program := [.class "rank0", .class "rank1" [.named "rank0"], .class "rank2" [.named "rank1"]]

/-- Priority tags: each tag derives from the one below, and the overload
for the nearest base wins. -/
def priorityTagNearest : Case :=
  { name := "priority_tag_nearest"
    cite := cite "over.ics.rank#4"
    program := tags ++ [.function "f" [rank0], .function "f" [rank1]]
    query := .call "f" [{ ty := rank2 }] (.selected 1)
    source := "computed by resolve" }

/-- Priority-tag dispatch over templates: a constrained overload at the
higher tag, and a fallback at the lower, which is a non-dependent
parameter checked for convertibility during deduction. -/
private def tagDispatch : Program :=
  tags ++
    [ .class "X", .concept "class_like" "std::is_class_v<T>"
    , .functionTemplate { name := "g", head := [typeParam], params := [T, rank1]
                          constraint := some (.atomic "class_like" [T]) }
    , .functionTemplate { name := "g", head := [typeParam], params := [T, rank0] } ]

/-- With the condition met, the constrained overload wins on the tag. -/
def priorityTagDispatch : Case :=
  { name := "priority_tag_dispatch"
    cite := cite "over.ics.rank#4"
    program := tagDispatch
    query := .call "g" [{ ty := X }, { ty := rank1 }] (.selected 0)
    source := "computed by resolve"
    atomics := [("class_like", [X], true)] }

/-- With it unmet, the constraint removes it and the fallback is viable
through the derived-to-base conversion of its non-dependent
parameter. -/
def priorityTagFallback : Case :=
  { name := "priority_tag_fallback"
    cite := cite "temp.deduct.general#5.sentence-8"
    program := tagDispatch
    query := .call "g" [{ ty := int }, { ty := rank1 }] (.selected 1)
    source := "computed by resolve"
    atomics := [("class_like", [int], false)] }

/-! ### Mandates -/

private def mandateConcepts : List Decl :=
  [.concept "class_like" "std::is_class_v<T>", .concept "integral_like" "std::is_integral_v<T>"]
private def mandateAtomics : List (String × List Ty × Bool) :=
  [("class_like", [.named "X"], true), ("integral_like", [.named "X"], false)]

/-- A Mandate that is met: the call is well-formed. -/
def mandateMet : Case :=
  { name := "mandate_met"
    cite := cite "structure.specifications#3"
    program := [.class "X"] ++ mandateConcepts ++
      [.functionTemplate { name := "f", head := [typeParam], params := [T], mandate := some (.atomic "class_like" [T]) }]
    query := .call "f" [{ ty := .named "X" }] (.selected 0)
    source := "computed by invoke"
    atomics := mandateAtomics }

/-- A Mandate that is not met: the selected function makes the program
ill-formed. -/
def mandateUnmet : Case :=
  { name := "mandate_unmet"
    cite := cite "structure.specifications#3"
    program := [.class "X"] ++ mandateConcepts ++
      [.functionTemplate { name := "f", head := [typeParam], params := [T], mandate := some (.atomic "integral_like" [T]) }]
    query := .call "f" [{ ty := .named "X" }] (.illFormed "a Mandate of the selected function is not met")
    source := "computed by invoke"
    atomics := mandateAtomics }

private def pointerOverloads (promoted : Bool) : Program :=
  let first : FunctionTemplate :=
    { name := "f", head := [typeParam], params := [.ptr T], mandate := some (.atomic "integral_like" [T]) }
  [.class "X"] ++ mandateConcepts ++
    [ .functionTemplate (if promoted then promote first else first)
    , .functionTemplate { name := "f", head := [typeParam], params := [T] } ]

/-- A Mandate does not fall back: the more specialized template is
selected, and its unmet Mandate makes the call ill-formed although the
other template would do. -/
def mandateNoFallback : Case :=
  { name := "mandate_no_fallback"
    cite := cite "structure.specifications#3"
    program := pointerOverloads false
    query := .call "f" [{ ty := .ptr (.named "X") }] (.illFormed "a Mandate of the selected function is not met")
    source := "computed by invoke"
    atomics := mandateAtomics }

/-- Promoted to a constraint, it removes the candidate, and the call moves
to the next best. -/
def promotedFallsBack : Case :=
  { name := "constraint_promotion_falls_back"
    cite := cite "structure.specifications#3"
    program := pointerOverloads true
    query := .call "f" [{ ty := .ptr (.named "X") }] (.selected 1)
    source := "computed by invoke"
    atomics := mandateAtomics }

/-- Before promotion: the constrained template is more constrained than
the one with the Mandate, and is selected. -/
def promotionBefore : Case :=
  { name := "constraint_promotion_before"
    cite := cite "temp.func.order#8"
    program := promotionProgram false
    query := .call "g" [{ ty := .named "X" }] (.selected 0)
    source := "computed by invoke"
    atomics := promotionAtomics }

/-- After promotion: neither constraint subsumes the other, and the call
is ambiguous. -/
def promotionAfter : Case :=
  { name := "constraint_promotion_reorders"
    cite := cite "temp.func.order#8"
    program := promotionProgram true
    query := .call "g" [{ ty := .named "X" }] (.ambiguous [0, 1])
    source := "computed by invoke"
    atomics := promotionAtomics }

/-! ### sfinae-requires -/

/-- A requires-clause is more constrained than no constraint, and wins. -/
def sfinaeRequiresOrdered : Case :=
  { name := "sfinae_requires_subsumes"
    cite := cite "temp.func.order#8"
    program := subsumptionProgram false
    query := .call "g" [{ ty := .named "X" }] (.selected 1)
    source := "computed by invoke"
    atomics := subsumptionAtomics }

/-- The same condition as `enable_if` in the return type is no
constraint: the call is ambiguous. -/
def sfinaeEnableIfUnordered : Case :=
  { name := "sfinae_enable_if_unordered"
    cite := cite "temp.func.order#8"
    program := subsumptionProgram true
    query := .call "g" [{ ty := .named "X" }] (.ambiguous [0, 1])
    source := "computed by invoke"
    atomics := subsumptionAtomics }

/-- The `enable_if` form is viable when its condition holds. -/
def sfinaeEnableIfViable : Case :=
  { name := "sfinae_enable_if_viable"
    cite := cite "temp.deduct.general#8.sentence-1"
    program := [.class "X", .concept "empty_like" "std::is_empty_v<T>"
      , .functionTemplate (enableIfForm { name := "g", head := [typeParam], params := [T] } "empty_like" [T])]
    query := .call "g" [{ ty := .named "X" }] (.selected 0)
    source := "computed by invoke"
    atomics := subsumptionAtomics }

/-- And not viable when it fails, as the requires form would not be. -/
def sfinaeEnableIfNotViable : Case :=
  { name := "sfinae_enable_if_not_viable"
    cite := cite "temp.deduct.general#8.sentence-1"
    program := [.class "X", .concept "integral_like" "std::is_integral_v<T>"
      , .functionTemplate (enableIfForm { name := "g", head := [typeParam], params := [T] } "integral_like" [T])]
    query := .call "g" [{ ty := .named "X" }] .noMatch
    source := "computed by invoke"
    atomics := shieldAtomics }

/-- The requires-clause shields the function type: the call is not
viable. -/
def sfinaeRequiresShields : Case :=
  { name := "sfinae_requires_shields"
    cite := cite "temp.deduct.general#5.sentence-6"
    program := shieldProgram false
    query := .call "f" [{ ty := .named "X" }, { ty := .named "int" }] .noMatch
    source := "computed by invoke"
    atomics := shieldAtomics }

/-- `enable_if` in the return type does not: the parameter's hard error
comes first. -/
def sfinaeEnableIfUnshielded : Case :=
  { name := "sfinae_enable_if_unshielded"
    cite := cite "temp.deduct.general#5.sentence-9"
    program := shieldProgram true
    query := .call "f" [{ ty := .named "X" }, { ty := .named "int" }]
      (.illFormed "static_assert in the primary trait<X>")
    source := "computed by invoke"
    atomics := shieldAtomics }

/-! ### dispatch-styles -/

/-- The if-constexpr encoding as C++: one template whose body tests the
conditions in order, branch `i` returning `selected<i>`, and ending in a
`static_assert` when no branch is taken. The return type is deduced, so
naming the call's type instantiates the body. -/
def ifConstexprCpp (conds : List Constraint) : String :=
  let branches := conds.zipIdx.map fun (c, i) =>
    s!"if constexpr ({constraint c}) return selected<{i}>\{};"
  "template <class T0>\nauto g(T0) {\n    " ++ String.intercalate "\n    else " branches ++
    "\n    else static_assert(sizeof(T0) == 0, \"no branch is taken\");\n}\n"

/-- An if-constexpr case, its expectation computed by `ifConstexpr`. -/
def ifConstexprCase (name : String) (p : Program) (atomics : List (String × List Ty × Bool))
    (conds : List Constraint) : Case :=
  let call := "decltype(g(std::declval<X>()))"
  match ifConstexprBranch p atomics conds with
  | .ok i =>
    { name, cite := cite "stmt.if#2.sentence-2", program := p, atomics
      query := .raw (ifConstexprCpp conds ++ s!"static_assert(std::is_same_v<{call}, selected<{i}>>);\n")
      source := "computed by ifConstexpr" }
  | _ =>
    { name, cite := cite "stmt.if#2.sentence-2", program := p, atomics
      query := .raw (ifConstexprCpp conds ++ s!"using probe = {call};\n") (wellFormed := false)
      source := "computed by ifConstexpr" }

private def dispatchOne : List Bool := [false, true, true]
private def dispatchNone : List Bool := [false, false, false]
private def dispatchFirst : List Bool := [true, false, false]
private def condList : List Constraint := [cond 0, cond 1, cond 2]

/-- Exclusion selects the first condition that holds. -/
def dispatchExclusionOne : Case :=
  { name := "dispatch_exclusion_first_true"
    cite := cite "temp.constr.op#2"
    program := exclusionProgram dispatchOne
    query := .call "g" [{ ty := .named "X" }] (.selected 1)
    source := "computed by invoke"
    atomics := condAtomics dispatchOne }

/-- So do priority tags. -/
def dispatchTagsOne : Case :=
  { name := "dispatch_tags_first_true"
    cite := cite "over.ics.rank#4"
    program := tagsProgram dispatchOne
    query := .call "g" [{ ty := .named "X" }, { ty := .named "rank2" }] (.selected 1)
    source := "computed by invoke"
    atomics := condAtomics dispatchOne }

/-- So does the if-constexpr chain. -/
def dispatchIfConstexprOne : Case :=
  ifConstexprCase "dispatch_if_constexpr_first_true" ((exclusionProgram dispatchOne).take 4)
    (condAtomics dispatchOne) condList

/-- With no condition holding, exclusion leaves the call not viable. -/
def dispatchExclusionNone : Case :=
  { name := "dispatch_exclusion_none"
    cite := cite "over.match.viable#3.sentence-1"
    program := exclusionProgram dispatchNone
    query := .call "g" [{ ty := .named "X" }] .noMatch
    source := "computed by invoke"
    atomics := condAtomics dispatchNone }

/-- So do priority tags. -/
def dispatchTagsNone : Case :=
  { name := "dispatch_tags_none"
    cite := cite "over.match.viable#3.sentence-1"
    program := tagsProgram dispatchNone
    query := .call "g" [{ ty := .named "X" }, { ty := .named "rank2" }] .noMatch
    source := "computed by invoke"
    atomics := condAtomics dispatchNone }

/-- The if-constexpr chain is ill-formed. -/
def dispatchIfConstexprNone : Case :=
  ifConstexprCase "dispatch_if_constexpr_none" ((exclusionProgram dispatchNone).take 4)
    (condAtomics dispatchNone) condList

/-- A last condition that fails hard when checked: exclusion never checks
it. -/
def dispatchExclusionHard : Case :=
  { name := "dispatch_exclusion_hard_last"
    cite := cite "temp.constr.op#2"
    program := .lookupHard "trait" :: exclusionProgram dispatchFirst hardLast
    query := .call "g" [{ ty := .named "X" }] (.selected 0)
    source := "computed by invoke"
    atomics := condAtomics dispatchFirst }

/-- Priority tags check it, and the call is ill-formed. -/
def dispatchTagsHard : Case :=
  { name := "dispatch_tags_hard_last"
    cite := cite "temp.constr.atomic#3.sentence-2"
    program := .lookupHard "trait" :: tagsProgram dispatchFirst hardLast
    query := .call "g" [{ ty := .named "X" }, { ty := .named "rank2" }]
      (.illFormed "static_assert in the primary trait<X>")
    source := "computed by invoke"
    atomics := condAtomics dispatchFirst }

/-- The if-constexpr chain never checks it. -/
def dispatchIfConstexprHard : Case :=
  ifConstexprCase "dispatch_if_constexpr_hard_last"
    ((exclusionProgram dispatchFirst).take 4 ++ [.lookupHard "trait"])
    (condAtomics dispatchFirst) [cond 0, cond 1, hardLast]

/-! ### Access to a base class -/

/-- Resolution ignores access, so the function naming the protected
implementation is selected, and the call is ill-formed. -/
def protectedBaseSelected : Case :=
  { name := "access_protected_base_selected"
    cite := cite "conv.ptr#3.sentence-2"
    program := protectedProgram
    query := .call "use" [{ ty := .named "map", lvalue := true }]
      (.illFormed "conversion to an inaccessible base class")
    source := "computed by Program.call" }

/-- Deduction from a derived class goes through the protected base, and
the selected call is ill-formed. -/
def protectedBaseDeduced : Case :=
  { name := "access_protected_base_deduced"
    cite := cite "temp.deduct.call#4"
    program := protectedTemplateProgram
    query := .call "use" [{ ty := .named "int_map", lvalue := true }]
      (.illFormed "conversion to an inaccessible base class")
    source := "computed by Program.call" }

/-- With the base public, the same call is well-formed. -/
def publicBaseSelected : Case :=
  { name := "access_public_base_selected"
    cite := cite "class.access.base#4"
    program := [ .class "impl", .class "derive_impl" [.named "impl"], .class "map" [.named "derive_impl"]
      , .function "use" [.lref (.const (.named "impl"))] ]
    query := .call "use" [{ ty := .named "map", lvalue := true }] (.selected 0)
    source := "computed by Program.call" }

/-- Every case of the Standard side. -/
def cases : List Case :=
  [ draftDeductCall3_rvalue, draftDeductCall3_lvalue, forwardingLvalue, forwardingRvalue
  , specialization, pointerMismatch, inconsistent, nonTemplatePreferred, redeclarationNotOverload
  , draftDeductGeneral5_both, draftDeductGeneral5_default, draftDeductGeneral5_undeduced
  , draftDeductGeneral5_explicit, draftDeductGeneral5_explicitBoth
  , draftDeductGeneral5_stepOrder, draftDeductGeneral8_immediate, stepOrderHazard
  , stepOrderHazardGuarded, stepOrderSoft, draftConstrAtomic3_betterMatch, tieBreakA
  , tieBreakB, tieBreakC, tieBreakD, refTieBreak, cvTieBreak, pointerMoreSpecialized
  , instanceMoreSpecialized, instanceAmbiguous, instancePrimary, rankDerivedToBase
  , rankReferenceExact, rankRvalueBinding, rankLvalueBinding, rankQualification
  , rankValueReferenceAmbiguous, priorityTagNearest, priorityTagDispatch, priorityTagFallback
  , mandateMet, mandateUnmet, mandateNoFallback, promotedFallsBack, promotionBefore
  , promotionAfter, sfinaeRequiresOrdered, sfinaeEnableIfUnordered, sfinaeEnableIfViable
  , sfinaeEnableIfNotViable, sfinaeRequiresShields, sfinaeEnableIfUnshielded
  , dispatchExclusionOne, dispatchTagsOne, dispatchIfConstexprOne, dispatchExclusionNone
  , dispatchTagsNone, dispatchIfConstexprNone, dispatchExclusionHard, dispatchTagsHard
  , dispatchIfConstexprHard, protectedBaseSelected, protectedBaseDeduced, publicBaseSelected ]

/-- Bindings in head order, for comparison. -/
def normalize (arity : Nat) (σ : Bindings) : List (ParamIdx × Ty) :=
  (List.range arity).filterMap fun i => (σ.lookup i).map (i, ·)

/-- How a case's program becomes an environment: the program's own
(`Env.ofProgram`) for the Standard side's cases, or a layer's extension
of it. -/
abbrev EnvOf := Program → List (String × List Ty × Bool) → Env

/-- For a deduction case, what the model computes, so that the stated
expectation and the computed one can be compared in the tests: `some
(some σ)` for success, `some none` for a deduction failure, and `none`
when the case is not a deduction case or the outcome was a hard error. -/
def computedWith (envOf : EnvOf) (c : Case) : Option (Option (List (ParamIdx × Ty))) :=
  match c.query with
  | .deduction callee as _ explicit =>
    match c.program.functionTemplate? callee with
    | some ft =>
      match deduceTemplate (envOf c.program c.atomics) ft explicit as with
      | .ok s => some (some (normalize ft.head.length s.args))
      | .soft _ => some none
      | .hard _ => none
    | none => none
  | _ => none

/-- For a call case, what the model computes for the call under the text:
resolution, the access check on the selected function's conversions, and
the selected function's Mandates, as candidate indices; `none` when the
case is not a call case. -/
def computedCallWith (envOf : EnvOf) (c : Case) : Option (Resolution Nat) :=
  match c.query with
  | .call callee as _ explicit =>
    some ((c.program.call (envOf c.program c.atomics) (c.program.overloadSet callee) as explicit).map
      (·.index))
  | _ => none

/-- The Standard side's cases are computed in the program's own
environment. -/
def computed (c : Case) : Option (Option (List (ParamIdx × Ty))) :=
  computedWith (fun p a => Env.ofProgram p a) c

def computedCall (c : Case) : Option (Resolution Nat) :=
  computedCallWith (fun p a => Env.ofProgram p a) c

/-- For a lookup case, what the model computes. -/
def computedLookup (c : Case) : Option (Resolution Nat) :=
  match c.query with
  | .lookup tc a _ => some (c.program.selectInstance tc a)
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
