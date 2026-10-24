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
import Overload.Names
import Overload.Adl
import Overload.Members
import Overload.DependentCandidate

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
      (explicit : List Ty := []) (scope : Scope := [])
  /-- Hand-written C++ with its own assertions, and whether it is
  well-formed. -/
  | raw (cpp : String) (wellFormed : Bool := true)
  /-- Which partial specialization of the lookup variable template `name`
  the argument selects; `expected` indexes the program's partial
  specializations of it, in order, `noMatch` is the primary, and
  `ambiguous` is ill-formed. -/
  | lookup (name : String) (arg : Ty) (expected : Resolution Nat)
  /-- Resolve a member call `obj.callee(args)` on an object of class
  `cls`; `expected` names the candidate by its index among the members
  found. -/
  | memberCall (cls callee : String) (args : List CallArg) (expected : Resolution Nat)
      (explicit : List Ty := [])
  /-- Resolve the dependent call declared at position `pos` of the
  program, instantiated with the arguments it carries; `expected` names
  the candidate by its index among the declarations its two contexts
  find. -/
  | dependentCall (pos : Nat) (expected : Resolution Nat)
  /-- Ask a type trait of the argument types; `expected` is the model's
  answer, asserted against the `std::` trait. -/
  | trait (q : Trait) (args : List Ty) (expected : Bool)
  deriving Repr, Inhabited

/-- The fixture every emitted unit declares: `deduced<...>` and
`value_of<V>` carry deduced arguments, `ref_of<R>` a deduced reference,
and `instance_of<T>` is the model's name for a selected specialization's
value. -/
def commonPrelude : String :=
  "template <class...> struct deduced {};\n" ++
  "template <auto V> struct value_of {};\n" ++
  "template <class T> struct instance_of {};\n" ++
  "template <const auto &R> struct ref_of {};\n" ++
  "template <int J> struct hidden {};\n"

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
  | .call _ _ (.illFormed _) _ _ => false
  | .call .. => true
  | .raw _ wf => wf
  | .lookup _ _ (.ambiguous _) | .lookup _ _ (.illFormed _) => false
  | .lookup .. => true
  | .memberCall _ _ _ (.illFormed _) _ => false
  | .memberCall .. => true
  | .dependentCall _ (.illFormed _) => false
  | .dependentCall _ (.selected _) => true
  | .dependentCall pos _ => !c.program.contains (.refersTo pos)
  | .trait .. => true

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
  | .fn ps r => s!"{ty r}({argList ps})"
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
  | .trait q m => s!"{q.spelling}<{String.intercalate ", " (m.map ty)}>"
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
  let parts := h.zipIdx.map fun (p, i) =>
    match σ.lookup i with
    | some (.value v) =>
      -- A converted integer value has the parameter's type, so the
      -- expectation casts the literal to it.
      match p.kind, v with
      | .const (.named n), .int _ | .const (.named n), .bool _ =>
        if isInteger n then s!"value_of<static_cast<{n}>({val v})>" else s!"value_of<{val v}>"
      | _, _ => s!"value_of<{val v}>"
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
def declarator (ft : FunctionTemplate) (r : String) (ps : String) (cv : String := "") : String :=
  match ft.ret with
  | .enableIf c as _ => s!"auto {ft.name}({ps}){cv} -> {ty (.enableIf c as (.named r))}"
  | _ => s!"{r} {ft.name}({ps}){cv}"

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

/-- Wrap C++ in the namespaces of a scope, outermost first. A class step
is rendered by its class, which a later stage supplies; here it is
passed over. -/
def inScope (s : Scope) (text : String) : String :=
  s.foldr (fun step acc =>
    match step with
    | .namespace n => s!"namespace {n} \{\n{acc}}\n"
    | .class _ => acc) text

/-- The return type each function of a program gets, by position:
`ret k` when `index` gives it `k`, the position of its entity among the
declarations the call's lookup finds; `hidden<j>` for a function of the
callee's name lookup does not find, so that hidden overloads keep
distinct types; `void` otherwise. -/
def returnTypes (p : Program) (callee : String) (ret : Nat → Head → String)
    (index : Decl → Option Nat) : Array String := Id.run do
  let mut rs := #[]
  let mut hidden := 0
  for d in p do
    let (name, h) := match d with
      | .function n _ _ => (some n, [])
      | .functionTemplate ft => (some ft.name, ft.head)
      | _ => (none, [])
    match name with
    | none => rs := rs.push ""
    | some n =>
      match index d with
      | some k => rs := rs.push (ret k h)
      | none =>
        if n = callee then
          rs := rs.push s!"hidden<{hidden}>"
          hidden := hidden + 1
        else rs := rs.push "void"
  return rs

/-- A function or function template, as a declaration with the return
type `r`, a member when `cv` is ` const`. -/
def functionText (d : Decl) (r : String) (cv : String := "") : String :=
  match d with
  | .function n ps _ => s!"{r} {n}({params ps}){cv};\n"
  | .functionTemplate ft =>
    let req := match ft.constraint with
      | some c => s!"\n    requires {constraint c}"
      | none => ""
    s!"{head ft.head}{req}\n{declarator ft r (params ft.params ft.defaultArgs) cv}{body ft r}\n"
  | _ => ""

/-- Is the class a type names, if any, defined before position `i` of
the program? A class the program does not declare comes from a prelude,
complete from the start. A reference to a class needs only a
declaration, which every class has up front. -/
def completeBefore (p : Program) (i : Nat) : Ty → Bool
  | .named n =>
    let isClass : Decl → Bool := fun | .class m .. => m == n | _ => false
    !p.any isClass || (p.take i).any isClass
  | .const t => completeBefore p i t
  | .lref _ | .rref _ | .ptr _ => true
  | _ => true

/-- The user-declared special member functions of a class, as member
declarations in its body: `= default`, `= delete`, or a body that does
nothing, which is what a user-provided one of the fragment is. -/
def specialsText (n : String) (ss : List SmfDecl) : String :=
  String.join (ss.map fun s =>
    let cv := if s.constParam then "const " else ""
    let head := match s.kind with
      | .defaultCtor => s!"constexpr {n}()"
      | .copyCtor => s!"constexpr {n}(const {n}&)".replace "const " cv
      | .moveCtor => s!"constexpr {n}(const {n}&&)".replace "const " cv
      | .copyAssign => s!"constexpr {n}& operator=(const {n}&)".replace "const " cv
      | .moveAssign => s!"constexpr {n}& operator=(const {n}&&)".replace "const " cv
      | .dtor => s!"constexpr ~{n}()"
    let body := match s.body, s.kind with
      | .defaulted, _ => " = default;"
      | .deleted, _ => " = delete;"
      | .userProvided, .copyAssign | .userProvided, .moveAssign => " { return *this; }"
      | .userProvided, _ => " {}"
    s!"    {head}{body}\n")

/-- The user-defined conversions of a class, as member declarations in its
body. A converting constructor is defined, with an empty body, so that it
serves a constant template argument; a conversion function is defined
when its target is complete and declared otherwise, since the cases call
in unevaluated contexts where a declaration serves. A class that needs a
default constructor beside a converting constructor declares one as a
special member, `= default`, since a user-declared constructor suppresses
the implicit one ([class.default.ctor]/1). -/
def conversionsText (p : Program) (i : Nat) (n : String) (convs : List UserConv) : String :=
  let keyword (e : Bool) := if e then "explicit " else ""
  String.join (convs.map fun
    | .constructor param e =>
      if completeBefore p i param then s!"    {keyword e}constexpr {n}({ty param}) \{}\n"
      else s!"    {keyword e}constexpr {n}({ty param});\n"
    | .function t e c =>
      let body := if completeBefore p i t then " { return {}; }" else ";"
      s!"    {keyword e}constexpr operator {ty t}(){if c then " const" else ""}{body}\n")

/-- The declarations of a program, as C++, each in its namespaces, with
the members of a class in its body. -/
def program (p : Program) (callee : String) (ret : Nat → Head → String)
    (index : Decl → Option Nat) : String := Id.run do
  let rs := returnTypes p callee ret index
  let mut out := ""
  let mut instances : List (String × Nat) := []
  -- Every class is declared first, so a conversion or a parameter can
  -- name a class defined later, as the draft's examples do.
  for d in p do
    match d with
    | .class n _ _ sc => if !d.isMember then out := out ++ inScope sc s!"struct {n};\n"
    | _ => pure ()
  for (d, i) in p.zipIdx do
    if d.isMember then continue
    let mut text := ""
    match d with
    | .class n bases prot sc =>
      let specs := bases.map (s!"public {ty ·}") ++ prot.map (s!"protected {ty ·}")
      let inherit := if specs.isEmpty then "" else s!" : {String.intercalate ", " specs}"
      let members := p.zipIdx.filter fun (m, _) => m.scope == sc ++ [.class n]
      let q := String.join (sc.filterMap fun | .namespace m => some s!"{m}::" | .class _ => none)
      let ofClass (c : Ty) : Bool := c == .named n || c == .named (q ++ n)
      let convs := p.filterMap fun
        | .converting c conv => if ofClass c then some conv else none
        | _ => none
      let data := p.filterMap fun
        | .member c m => if ofClass c then some m else none
        | _ => none
      let specials := p.filterMap fun
        | .special c s => if ofClass c then some s else none
        | _ => none
      if members.isEmpty && convs.isEmpty && data.isEmpty && specials.isEmpty then
        text := s!"struct {n}{inherit} \{};\n"
      else
        let fields := String.join (data.map fun m =>
          let init := if m.init then " {}" else ""
          s!"    {ty m.ty} {m.name}{init};\n")
        let body := String.join (members.map fun (m, j) =>
          "    " ++ (functionText m (rs.getD j "void") " const").replace "\n    " "\n        ")
        text := s!"struct {n}{inherit} \{\n{fields}{body}{specialsText n specials}{conversionsText p i n convs}};\n"
    | .classTemplate n h _ => text := s!"{head h}\nstruct {n} \{};\n"
    | .function .. | .functionTemplate _ => text := functionText d (rs.getD i "void")
    | .lookup c =>
      text := s!"template <class T>\ninline constexpr auto {c} = std::false_type\{};\n"
    | .lookupHard c =>
      text := s!"template <class T>\nstruct {c}_instance \{\n"
      text := text ++ s!"    static_assert(sizeof(T) == 0, \"no {c} instance for this type\");\n"
      text := text ++ s!"    static constexpr int value = 0;\n};\n"
      text := text ++ s!"template <class T>\ninline constexpr auto {c} = {c}_instance<T>::value;\n"
    | .instance c h pat =>
      let k := (instances.find? (·.1 == c)).map (·.2) |>.getD 0
      instances := (c, k + 1) :: instances.filter (·.1 != c)
      text := s!"{head h}\ninline constexpr selected<{k}> {c}<{ty pat}>\{};\n"
    | .concept n body =>
      text := s!"template <class T>\nconcept {n} = {body};\n"
    | .use c t =>
      text := s!"static_assert(sizeof({c}<{ty t}>) > 0);\n"
    | .object n cls _ =>
      text := s!"inline constexpr {cls} {n}\{};\n"
    | .dependentCall callee _ _ =>
      text := s!"template <class... A>\nauto dependent_{i}(A&&... a) -> decltype({callee}(static_cast<A&&>(a)...));\n"
    | .refersTo call =>
      match p[call]? with
      | some (.dependentCall _ as _) =>
        text := s!"using reference_{i} = decltype({callExpr s!"dependent_{call}" [] as});\n"
      | _ => text := ""
    | .converting .. | .member .. | .special .. => text := ""
    out := out ++ inScope d.scope text
  return out

/-- The declarations a query's call resolves over, one per entity, in the
order `Candidate.index` numbers them: what the call's lookup finds, the
call operators of the object it finds, or the members a member call
finds. -/
def foundEntities (p : Program) : Query → List Decl
  | .call callee as _ _ scope =>
    match p.callCandidates p.length scope callee as with
    | .selected fs => fs
    | _ => []
  | .memberCall cls callee _ _ _ =>
    match p.memberSearch p.length cls callee with
    | .selected ms => entities ms
    | _ => []
  | .dependentCall pos _ =>
    match p[pos]? with
    | some (.dependentCall callee args s) =>
      match p.dependentCandidates pos s callee args with
      | .selected fs => fs
      | _ => []
    | _ => []
  | _ => []

/-! ### Qualified names

A class declared in a namespace is spelled `N::X` from anywhere else, and
spelling it so inside `N` is valid too. The model names a class by its
name alone, so before rendering every type in a case is rewritten to
name each class and class template by its qualified name. Class steps in
a scope are passed over, as `inScope` passes them. -/

/-- The qualified name of a scope's namespaces, `a::b::`. -/
def qualifier (s : Scope) : String :=
  String.join (s.filterMap fun
    | .namespace n => some s!"{n}::"
    | .class _ => none)

/-- The classes and class templates of a program in a namespace, with
their qualifiers. -/
def qualifiers (p : Program) : List (String × String) :=
  p.filterMap fun
    | .class n _ _ s => if s.isEmpty then none else some (n, qualifier s)
    | .classTemplate n _ s => if s.isEmpty then none else some (n, qualifier s)
    | _ => none

/-- Qualify every class and class template name in a type. -/
partial def qualifyTy (q : List (String × String)) : Ty → Ty
  | .named n => .named (((q.lookup n).getD "") ++ n)
  | .spec c as => .spec (((q.lookup c).getD "") ++ c) (qualifyTy q as)
  | .const t => .const (qualifyTy q t)
  | .ptr t => .ptr (qualifyTy q t)
  | .lref t => .lref (qualifyTy q t)
  | .rref t => .rref (qualifyTy q t)
  | .cons a as => .cons (qualifyTy q a) (qualifyTy q as)
  | .nondeduced t => .nondeduced (qualifyTy q t)
  | .lookup n a => .lookup n (qualifyTy q a)
  | .ref t => .ref (qualifyTy q t)
  | .removeCvref t => .removeCvref (qualifyTy q t)
  | .typeOf t => .typeOf (qualifyTy q t)
  | .enableIf c as t => .enableIf c (qualifyTy q as) (qualifyTy q t)
  | .fn ps r => .fn (qualifyTy q ps) (qualifyTy q r)
  | t => t

/-- Qualify the types of a template parameter. -/
def qualifyParam (q : List (String × String)) (tp : TemplateParam) : TemplateParam :=
  { kind := match tp.kind with
      | .type => .type
      | .const t => .const (qualifyTy q t)
    default := tp.default.map (qualifyTy q) }

/-- Qualify the types a constraint maps. -/
def qualifyConstraint (q : List (String × String)) : Constraint → Constraint
  | .atomic e ts => .atomic e (ts.map (qualifyTy q))
  | .trait tr ts => .trait tr (ts.map (qualifyTy q))
  | .conj a b => .conj (qualifyConstraint q a) (qualifyConstraint q b)
  | .disj a b => .disj (qualifyConstraint q a) (qualifyConstraint q b)

/-- Qualify the types of a declaration; its own name stays as declared. -/
def qualifyDecl (q : List (String × String)) : Decl → Decl
  | .class n bs ps s => .class n (bs.map (qualifyTy q)) (ps.map (qualifyTy q)) s
  | .classTemplate n h s => .classTemplate n (h.map (qualifyParam q)) s
  | .function n ps s => .function n (ps.map (qualifyTy q)) s
  | .functionTemplate ft =>
    .functionTemplate { ft with head := ft.head.map (qualifyParam q), params := ft.params.map (qualifyTy q)
                                ret := qualifyTy q ft.ret, constraint := ft.constraint.map (qualifyConstraint q)
                                mandate := ft.mandate.map (qualifyConstraint q) }
  | .instance c h pat => .instance c (h.map (qualifyParam q)) (qualifyTy q pat)
  | .use c t => .use c (qualifyTy q t)
  | .dependentCall callee as s => .dependentCall callee (as.map fun a => { a with ty := qualifyTy q a.ty }) s
  | .member c m => .member (qualifyTy q c) { m with ty := qualifyTy q m.ty }
  | .special c s => .special (qualifyTy q c) s
  | .converting c conv =>
    .converting (qualifyTy q c) (match conv with
      | .constructor param e => .constructor (qualifyTy q param) e
      | .function t e c => .function (qualifyTy q t) e c)
  | d => d

/-- Qualify the types of a case, program and query alike. -/
def qualifyCase (c : Case) : Case :=
  let q := qualifiers c.program
  let arg (a : CallArg) : CallArg := { a with ty := qualifyTy q a.ty }
  { c with
    program := c.program.map (qualifyDecl q)
    query := match c.query with
      | .deduction callee as expected explicit =>
        .deduction callee (as.map arg) expected (explicit.map (qualifyTy q))
      | .call callee as expected explicit scope =>
        .call callee (as.map arg) expected (explicit.map (qualifyTy q)) scope
      | .raw cpp wf => .raw cpp wf
      | .lookup tc a expected => .lookup tc (qualifyTy q a) expected
      | .memberCall cls callee as expected explicit =>
        .memberCall (((q.lookup cls).getD "") ++ cls) callee (as.map arg) expected
          (explicit.map (qualifyTy q))
      | .dependentCall pos expected => .dependentCall pos expected
      | .trait tr as expected => .trait tr (as.map (qualifyTy q)) expected }

/-- The whole translation unit for a case. The lookup that numbers the
candidates runs on the case as stated; the rendering uses qualified
names. -/
def render (c₀ : Case) : String := Id.run do
  let found := foundEntities c₀.program c₀.query
  let q := qualifiers c₀.program
  let found := found.map (qualifyDecl q)
  let c := qualifyCase c₀
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
    out := out ++ program p callee (fun _ h => deducedType h)
      (fun d => if d.name? = some callee then some 0 else none) ++ "\n"
    match expected with
    | some σ =>
      out := out ++ s!"static_assert(std::is_same_v<decltype({callExpr callee explicit as}), {expectedDeduced h σ}>);\n"
    | none =>
      out := out ++ notViable callee explicit as
  | .call callee as expected explicit scope =>
    out := out ++ program c.program callee (fun k _ => s!"selected<{k}>")
      (fun d => found.findIdx? (sameEntity · d)) ++ "\n"
    let mut q := ""
    match expected with
    | .selected k =>
      q := q ++ s!"static_assert(std::is_same_v<decltype({callExpr callee explicit as}), selected<{k}>>);\n"
    | .noMatch | .ambiguous _ =>
      q := q ++ notViable callee explicit as
    | .illFormed r =>
      q := q ++ s!"// the model expects a hard error: {r}\n"
      q := q ++ s!"using probe = decltype({callExpr callee explicit as});\n"
    if hasMandates c.program then
      match expected with
      | .selected _ | .illFormed _ => q := q ++ evaluatedCall callee explicit as
      | _ => pure ()
    out := out ++ inScope scope q
  | .raw cpp _ =>
    out := out ++ program c.program "" (fun _ _ => "void") (fun _ => none) ++ "\n" ++ cpp
  | .trait tr as expected =>
    out := out ++ program c.program "" (fun _ _ => "void") (fun _ => none) ++ "\n"
    let args := String.intercalate ", " (as.map ty)
    out := out ++ s!"static_assert({tr.spelling}<{args}> == {expected});\n"
  | .memberCall cls callee as expected explicit =>
    out := out ++ program c.program callee (fun k _ => s!"selected<{k}>")
      (fun d => found.findIdx? (sameEntity · d)) ++ "\n"
    let member := s!"std::declval<const {cls}&>().{callee}"
    match expected with
    | .selected k =>
      out := out ++ s!"static_assert(std::is_same_v<decltype({callExpr member explicit as}), selected<{k}>>);\n"
    | .noMatch | .ambiguous _ =>
      out := out ++ notViable member explicit as
    | .illFormed r =>
      out := out ++ s!"// the model expects a hard error: {r}\n"
      out := out ++ s!"using probe = decltype({callExpr member explicit as});\n"
  | .dependentCall pos expected =>
    let (callee, as) := match c.program[pos]? with
      | some (.dependentCall callee as _) => (callee, as)
      | _ => ("", [])
    out := out ++ program c.program callee (fun k _ => s!"selected<{k}>")
      (fun d => found.findIdx? (sameEntity · d)) ++ "\n"
    let dep := s!"dependent_{pos}"
    match expected with
    | .selected k =>
      out := out ++ s!"static_assert(std::is_same_v<decltype({callExpr dep [] as}), selected<{k}>>);\n"
      for (d, i) in c.program.zipIdx do
        if d == .refersTo pos then
          out := out ++ s!"static_assert(std::is_same_v<reference_{i}, selected<{k}>>);\n"
    | .noMatch | .ambiguous _ =>
      out := out ++ notViable dep [] as
    | .illFormed r =>
      out := out ++ s!"// the model expects a hard error: {r}\n"
      out := out ++ s!"using probe = decltype({callExpr dep [] as});\n"
  | .lookup tc a expected =>
    out := out ++ program c.program "" (fun _ _ => "void") (fun _ => none) ++ "\n"
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

/-! ### [basic.lookup.unqual]/2: an inner scope hides an outer one

Unqualified lookup stops at the first enclosing scope that binds the
name, so a declaration in an inner namespace hides every outer one,
whatever the signatures. The arguments are an `int` or a class of the
global namespace, so argument-dependent lookup adds nothing. -/

private def user : Scope := [.namespace "user"]
private def xClass : Ty := .named "X"

/-- `struct X {}; void f(int);` at global scope, `void f(X);` in `user`,
and `f(1)` written in `user`: the exact match outside is never a
candidate, and the call is not viable. -/
def innerHidesOuter : Case :=
  { name := "basic_lookup_unqual_2_inner_hides_outer"
    cite := cite "basic.lookup.unqual#2.sentence-1"
    program := hidingProgram
    query := .call "f" [{ ty := int }] .noMatch [] user
    source := "computed by resolve over unqualified lookup" }

/-- The same, called with an `X`: the inner declaration is selected. -/
def innerSelected : Case :=
  { name := "basic_lookup_unqual_2_inner_selected"
    cite := cite "basic.lookup.unqual#2.sentence-1"
    program := hidingProgram
    query := .call "f" [{ ty := xClass }] (.selected 0) [] user
    source := "computed by resolve over unqualified lookup" }

/-- The same declarations and the same call at global scope: the inner
declaration is not visible there, and the outer one is selected. -/
def outerAtGlobal : Case :=
  { name := "basic_lookup_unqual_2_outer_at_global"
    cite := cite "basic.lookup.unqual#2.sentence-1"
    program := hidingProgram
    query := .call "f" [{ ty := int }] (.selected 0)
    source := "computed by resolve over unqualified lookup" }

/-- `f(1)` written in `user`, which declares no `f`: the search continues
in the parent scope and finds the global declaration. -/
def parentFound : Case :=
  { name := "basic_lookup_unqual_2_parent_found"
    cite := cite "basic.lookup.unqual#2.sentence-2"
    program := [.function "f" [int], .function "g" [int] user]
    query := .call "f" [{ ty := int }] (.selected 0) [] user
    source := "computed by resolve over unqualified lookup" }

/-- `f(x)` written in `a::b`, with `f` declared in `a` and at global
scope and neither in `a::b`: the nearer enclosing scope wins. The global
`f(int)`, which argument-dependent lookup also reaches, is not viable for
an `X`. -/
def nearestEnclosing : Case :=
  { name := "basic_lookup_unqual_2_nearest_enclosing"
    cite := cite "basic.lookup.unqual#2.sentence-2"
    program := [ .class "X", .function "f" [int], .function "f" [xClass] [.namespace "a"]
               , .function "g" [int] [.namespace "a", .namespace "b"] ]
    query := .call "f" [{ ty := xClass }] (.selected 0) [] [.namespace "a", .namespace "b"]
    source := "computed by resolve over unqualified lookup" }

/-- No declaration of `f` precedes the call: lookup finds nothing and the
program is ill-formed. -/
def nothingFound : Case :=
  { name := "basic_lookup_general_1_nothing_found"
    cite := cite "basic.lookup.general#1.sentence-3"
    program := [.function "g" [int]]
    query := .call "f" [{ ty := int }] (.illFormed "no declaration of f is found") [] user
    source := "computed by lookup" }

/-! ### [basic.lookup.argdep]: argument-dependent lookup

A call written where unqualified lookup finds nothing, or finds only
functions, also finds the functions of the arguments' associated
namespaces: the class's namespace, its bases' namespaces, and for a
class template specialization its type arguments' namespaces. -/

private def N : Scope := [.namespace "N"]

/-- The example of [basic.lookup.argdep]/1: `namespace N { struct S { };
void f(S); }` and `f(s)` at global scope calls `N::f`. -/
def argdepExample : Case :=
  { name := "basic_lookup_argdep_1_example"
    cite := cite "basic.lookup.argdep#1"
    program := argdepProgram
    query := .call "f" [{ ty := .named "S", lvalue := true }] (.selected 0)
    source := "computed by resolve over the call's lookup" }

/-- With the operation a function template at global scope, a user's
`fmap(X)` beside the user's class is found through the argument's
namespace and wins as a non-template exact match. -/
def freeFunctionAdmitsAdl : Case :=
  { name := "basic_lookup_argdep_1_free_function_admits"
    cite := cite "basic.lookup.argdep#1"
    program := freeFunctionProgram
    query := .call "fmap" [{ ty := .named "X" }] (.selected 1)
    source := "computed by resolve over the call's lookup" }

/-- A base class's namespace is associated: `struct D : N::B {}` at
global scope, `void f(B);` in `N`, and `f(d)` at global scope selects it
through the derived-to-base conversion. -/
def adlThroughBase : Case :=
  { name := "basic_lookup_argdep_3_base"
    cite := cite "basic.lookup.argdep#3"
    program := [ .class "B" [] [] N, .function "f" [.named "B"] N, .class "D" [.named "B"] ]
    query := .call "f" [{ ty := .named "D", lvalue := true }] (.selected 0)
    source := "computed by resolve over the call's lookup" }

/-- A type template argument's namespace is associated: `box<N::S>` with
`box` at global scope reaches `void f(box<S>);` in `N`. -/
def adlThroughTemplateArgument : Case :=
  { name := "basic_lookup_argdep_3_template_argument"
    cite := cite "basic.lookup.argdep#3"
    program := [ .classTemplate "box" [typeParam], .class "S" [] [] N
               , .function "f" [.spec' "box" [.named "S"]] N ]
    query := .call "f" [{ ty := .spec' "box" [.named "S"], lvalue := true }] (.selected 0)
    source := "computed by resolve over the call's lookup" }

/-- A fundamental type has no associated namespace: `void f(int);` in
`N` is not found by `f(1)` at global scope, where nothing else declares
`f`, so the program is ill-formed. -/
def noAdlForFundamental : Case :=
  { name := "basic_lookup_argdep_3_fundamental"
    cite := cite "basic.lookup.argdep#3"
    program := [ .function "f" [int] N ]
    query := .call "f" [{ ty := int }] (.illFormed "no declaration of f is found")
    source := "computed by lookup" }

/-! ### [class.member.lookup] and [over.call.object]: members and objects

A class's own declarations of a name are the whole result of a search in
its scope, so a member of a derived class hides every base member of the
name; two unrelated bases that both declare it make the lookup
ambiguous; and a call on an object resolves over the call operators of
its class. -/

private def inClass (c : String) : Scope := [.class c]

/-- `struct A { void f(int); }; struct D : A { void f(X); };` and
`d.f(1)`: the base's exact match is hidden, and the call is not viable. -/
def derivedHidesBase : Case :=
  { name := "class_member_lookup_3_derived_hides_base"
    cite := cite "class.member.lookup#3.sentence-2"
    program := [ .class "X", .class "A", .function "f" [int] (inClass "A")
               , .class "D" [.named "A"], .function "f" [xClass] (inClass "D") ]
    query := .memberCall "D" "f" [{ ty := int }] .noMatch
    source := "computed by resolve over the member lookup" }

/-- `struct D : A {}` with no `f` of its own: the search continues into
the base. -/
def baseMemberFound : Case :=
  { name := "class_member_lookup_4_base_found"
    cite := cite "class.member.lookup#4.sentence-1"
    program := [ .class "A", .function "f" [int] (inClass "A"), .class "D" [.named "A"] ]
    query := .memberCall "D" "f" [{ ty := int }] (.selected 0)
    source := "computed by resolve over the member lookup" }

/-- The example of [class.member.lookup]/6, with functions for members:
`C` has two unrelated bases that declare `x`, and `c.x()` is ill-formed. -/
def ambiguousBases : Case :=
  { name := "class_member_lookup_6_ambiguous_bases"
    cite := cite "class.member.lookup#6.sentence-2"
    program := ambiguousBasesProgram
    query := .memberCall "C" "x" [] (.illFormed "the lookup of x in C is ambiguous")
    source := "computed by the member lookup" }

/-- `struct fn { void operator()(int) const; }; inline constexpr fn f{};`
and `f(1)`: the call resolves over the class's call operators. -/
def objectCall : Case :=
  { name := "over_call_object_1_call_operator"
    cite := cite "over.call.object#1.sentence-2"
    program := [ .class "fn", .function "operator()" [int] (inClass "fn"), .object "f" "fn" ]
    query := .call "f" [{ ty := int }] (.selected 0)
    source := "computed by resolve over the call operators" }

/-- With the operation the `operator()` of an object, a user's `fmap(X)`
beside the user's class is never a candidate: lookup binds `fmap` to the
object, which suppresses argument-dependent lookup. -/
def objectSuppressesAdl : Case :=
  { name := "basic_lookup_argdep_1_object_suppresses"
    cite := cite "basic.lookup.argdep#1"
    program := objectProgram
    query := .call "fmap" [{ ty := xClass }] (.selected 0)
    source := "computed by resolve over the call operators" }

/-! ### [temp.res.general]/1 and [basic.lookup.argdep]/4: dependent calls

A dependent call's name is looked up where it appears in the template's
definition, and argument-dependent lookup runs again from the
instantiation context, the end of the unit: a function declared after the
template is found through an argument's namespace, and never for a
fundamental type. The emitted template takes its arguments by forwarding
reference and names the call in a trailing return type, so the function
selected is observable and a lookup failure is a substitution failure. -/

/-- The example of [temp.res.general]/1, with `E` a class: `f(t)`
instantiated at `E` finds `f(E)`, declared after the template. -/
def dependentFindsLater : Case :=
  { name := "temp_res_general_1_dependent_finds_later"
    cite := cite "temp.res.general#1.sentence-2"
    program := resGeneral1Program
    query := .dependentCall 1 (.selected 1)
    source := "computed by resolve over the dependent call's lookup" }

/-- A function declared after the template, called with an `int`: not
found at the definition, and no associated namespace to find it at the
instantiation, so the call is ill-formed. -/
def dependentBoundAtDefinition : Case :=
  { name := "temp_res_general_1_bound_at_definition"
    cite := cite "temp.res.general#1.sentence-1"
    program := [ .dependentCall "f" [{ ty := int }], .function "f" [int] ]
    query := .dependentCall 0 (.illFormed "no declaration of f is found")
    source := "computed by the dependent call's lookup" }

/-- `N::f(S)` declared after the template is found from the instantiation
context through the argument's namespace. -/
def dependentInstantiationContext : Case :=
  { name := "basic_lookup_argdep_4_instantiation_context"
    cite := cite "basic.lookup.argdep#4.sentence-3"
    program := [ .class "S" [] [] N, .dependentCall "f" [{ ty := .named "S", lvalue := true }]
               , .function "f" [.named "S"] N ]
    query := .dependentCall 1 (.selected 0)
    source := "computed by resolve over the dependent call's lookup" }

/-- `N::f(S)` declared before the template, `g<S>` referred to by a
declaration, and `N::f(int)` declared after it: the specialization has a
point of instantiation after the referring declaration and another at
the unit's end, and the call selects `N::f(S)` at both. -/
def dependentReferencePoint : Case :=
  { name := "temp_point_1_reference_point"
    cite := cite "temp.point#1.sentence-2"
    program := [ .class "S" [] [] N, .function "f" [.named "S"] N
               , .dependentCall "f" [{ ty := .named "S", lvalue := true }], .refersTo 2
               , .function "f" [int] N ]
    query := .dependentCall 2 (.selected 0)
    source := "computed by resolve over the dependent call's lookup" }

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

/-! ### The conversion of a constant template argument -/

/-- `template <int> int f(int); template <signed char> int f(int);`, the
example of [temp.deduct.general]/12. -/
private def narrowingProgram : Program :=
  [ .functionTemplate { name := "f", head := [{ kind := .const int }], params := [int] }
  , .functionTemplate { name := "f", head := [{ kind := .const (.named "signed char") }], params := [int] } ]

/-- `f<1000>(0)`: a `signed char` cannot represent 1000, so substitution
fails for the second template and the first is selected. -/
def draftDeductGeneral12_narrowing : Case :=
  { name := "draft_temp_deduct_general_12_narrowing"
    cite := cite "temp.deduct.general#12"
    program := narrowingProgram
    query := .call "f" [{ ty := int }] (.selected 0) (explicit := [.value (.int 1000)])
    source := "computed by resolve" }

/-- `f<1>(0)`: 1 is not narrowing, both are viable, and neither is more
specialized: ambiguous. -/
def draftDeductGeneral12_ambiguous : Case :=
  { name := "draft_temp_deduct_general_12_ambiguous"
    cite := cite "temp.deduct.general#12"
    program := narrowingProgram
    query := .call "f" [{ ty := int }] (.ambiguous [0, 1]) (explicit := [.value (.int 1)])
    source := "computed by resolve" }

/-- `template <t> void f();` -/
private def constTemplate (t : Ty) : FunctionTemplate :=
  { name := "f", head := [{ kind := .const t }], params := [] }

/-- `template <bool> void f(); f<2>()`: the conversion of 2 to `bool`
narrows. -/
def boolNarrowing : Case :=
  { name := "bool_narrowing"
    cite := cite "dcl.init.list#7"
    program := [.functionTemplate (constTemplate (.named "bool"))]
    query := .deduction "f" [] none (explicit := [.value (.int 2)])
    source := "computed by deduceTemplate" }

/-- `f<1>()` on the same template: the parameter's value is `true`. -/
def boolConverted : Case :=
  { name := "bool_converted"
    cite := cite "temp.arg.nontype#2.sentence-2"
    program := [.functionTemplate (constTemplate (.named "bool"))]
    query := .deduction "f" [] (some [(0, .value (.bool true))]) (explicit := [.value (.int 1)])
    source := "computed by deduceTemplate" }

/-- `template <unsigned> void f(); f<-1>()`: narrowing. -/
def unsignedNarrowing : Case :=
  { name := "unsigned_narrowing"
    cite := cite "dcl.init.list#7"
    program := [.functionTemplate (constTemplate (.named "unsigned"))]
    query := .deduction "f" [] none (explicit := [.value (.int (-1))])
    source := "computed by deduceTemplate" }

/-- `template <int> void f(); f<true>()`: an integral promotion, the value
1. -/
def boolPromoted : Case :=
  { name := "bool_promoted"
    cite := cite "expr.const.const#8"
    program := [.functionTemplate (constTemplate int)]
    query := .deduction "f" [] (some [(0, .value (.int 1))]) (explicit := [.value (.bool true)])
    source := "computed by deduceTemplate" }

/-- `template <long> void f(); f<1>()`: an integral conversion that does
not narrow, the value 1 of type `long`. -/
def intToLong : Case :=
  { name := "int_to_long"
    cite := cite "expr.const.const#8"
    program := [.functionTemplate (constTemplate (.named "long"))]
    query := .deduction "f" [] (some [(0, .value (.int 1))]) (explicit := [.value (.int 1)])
    source := "computed by deduceTemplate" }

/-- `struct B {}; struct D : B {}; template <B> void f(); f<D{}>()`: the
temporary `constexpr B v = D{};` slices the argument to its `B`
subobject, and the parameter's value is `B{}`. -/
def derivedToBaseValue : Case :=
  { name := "derived_to_base_value"
    cite := cite "temp.arg.nontype#3.sentence-1"
    program := [.class "B", .class "D" [.named "B"], .functionTemplate (constTemplate (.named "B"))]
    query := .deduction "f" [] (some [(0, .value (.obj' "B" []))])
      (explicit := [.value (.obj' "D" [.obj' "B" []])])
    source := "computed by deduceTemplate" }

/-! ### Phase 11: user-defined conversions -/

private def cS : Ty := .named "S"
private def cT : Ty := .named "T"
/-- `T() = default;`, which a class with a converting constructor needs to
keep a default constructor. -/
private def defaultedCtor (c : Ty) : Decl := .special c { kind := .defaultCtor, body := .defaulted }
/-- `struct S {}; struct T { T(const S&); T() = default; };`. -/
private def ctorProgram : Program :=
  [.class "S", .class "T", .converting cT (.constructor (.lref (.const cS))), defaultedCtor cT]

/-- `void f(T); f(S{})`: the converting constructor forms a user-defined
conversion sequence, and the call selects `f`. -/
def userConversionSelected : Case :=
  { name := "user_conversion_selected"
    cite := cite "over.ics.user#1"
    program := ctorProgram ++ [.function "f" [cT]]
    query := .call "f" [{ ty := cS }] (.selected 0)
    source := "computed by Program.call" }

/-- `void f(T); template <class U> void f(const U&); f(S{})`: the template's
identity conversion beats the user-defined sequence, so the template wins
before the non-template preference is reached. -/
def userConversionLosesRank : Case :=
  { name := "user_conversion_loses_rank"
    cite := cite "over.ics.rank#2"
    program := ctorProgram ++
      [ .function "f" [cT]
      , .functionTemplate { name := "f", head := [{ kind := .type }], params := [.lref (.const (.param 0))] } ]
    query := .call "f" [{ ty := cS }] (.selected 1)
    source := "computed by Program.call" }

/-- `struct T {}; struct S { operator T() const; }; void f(T); f(S{})`: a
conversion function forms the sequence. -/
def conversionFunctionSelected : Case :=
  { name := "conversion_function_selected"
    cite := cite "class.conv.fct#2"
    program := [.class "T", .class "S", .converting cS (.function cT), .function "f" [cT]]
    query := .call "f" [{ ty := cS }] (.selected 0)
    source := "computed by Program.call" }

/-- `void f(const T&); f(S{})`: the converted temporary binds a reference to
const. -/
def convertedTemporaryBinds : Case :=
  { name := "converted_temporary_binds_const_ref"
    cite := cite "over.ics.ref#2"
    program := ctorProgram ++ [.function "f" [.lref (.const cT)]]
    query := .call "f" [{ ty := cS }] (.selected 0)
    source := "computed by Program.call" }

/-- `void f(T&); f(S{})`: an lvalue reference to non-const binds no
temporary, so no sequence forms. -/
def convertedTemporaryRefused : Case :=
  { name := "converted_temporary_refused_by_ref"
    cite := cite "over.ics.ref#3.sentence-1"
    program := ctorProgram ++ [.function "f" [.lref cT]]
    query := .call "f" [{ ty := cS }] .noMatch
    source := "computed by Program.call" }

/-- `struct T { explicit T(const S&); }; void f(T); f(S{})`: an explicit
constructor is no candidate for the copy-initialization of an argument. -/
def explicitConstructorNotCandidate : Case :=
  { name := "explicit_constructor_not_candidate"
    cite := cite "over.match.copy#1"
    program := [.class "S", .class "T", .converting cT (.constructor (.lref (.const cS)) true), defaultedCtor cT
               , .function "f" [cT]]
    query := .call "f" [{ ty := cS }] .noMatch
    source := "computed by Program.call" }

/-- `struct B {}; struct D : B {}; struct S { operator D() const; }; void
f(B); void f(D); f(S{})`: both go through the one conversion function, and
the second standard sequence decides, identity over derived-to-base. -/
def secondSequenceDecides : Case :=
  { name := "second_sequence_decides"
    cite := cite "over.ics.rank#3"
    program := [ .class "B", .class "D" [.named "B"], .class "S", .converting cS (.function (.named "D"))
               , .function "f" [.named "B"], .function "f" [.named "D"] ]
    query := .call "f" [{ ty := cS }] (.selected 1)
    source := "computed by Program.call" }

/-- The draft's example of [class.conv.general]/4: `struct X { operator
int(); }; struct Y { operator X(); }; void f(int); f(Y{})`: at most one
user-defined conversion applies, so `Y` to `X` to `int` is no sequence. -/
def conversionChainStops : Case :=
  { name := "class_conv_general_4_chain_stops"
    cite := cite "class.conv.general#4"
    program := [ .class "X", .class "Y", .converting (.named "X") (.function (.named "int"))
               , .converting (.named "Y") (.function (.named "X")), .function "f" [.named "int"] ]
    query := .call "f" [{ ty := .named "Y" }] .noMatch
    source := "computed by Program.call" }

/-- The draft's example of [over.best.ics.general]/12: `class A { A(B&); };
class B { operator A(); }; class C { C(B&); }; void f(A); void f(C); B b;
f(b)` is ambiguous, since `b` to `A` is the ambiguous conversion sequence,
indistinguishable from `b` to `C`. -/
def draftBestIcsAmbiguous : Case :=
  { name := "over_best_ics_general_12_ambiguous"
    cite := cite "over.best.ics.general#12"
    program := [ .class "B", .class "A", .class "C"
               , .converting (.named "A") (.constructor (.lref (.named "B")))
               , .converting (.named "B") (.function (.named "A") false false)
               , .converting (.named "C") (.constructor (.lref (.named "B")))
               , defaultedCtor (.named "A"), defaultedCtor (.named "C")
               , .function "f" [.named "A"], .function "f" [.named "C"] ]
    query := .call "f" [{ ty := .named "B", lvalue := true }] (.ambiguous [0, 1])
    source := "computed by Program.call" }

/-- The same with `void f(B)` added: the identity is a standard sequence
and beats both, so the call is unambiguous. -/
def draftBestIcsResolved : Case :=
  { name := "over_best_ics_general_12_resolved"
    cite := cite "over.best.ics.general#12"
    program := draftBestIcsAmbiguous.program ++ [.function "f" [.named "B"]]
    query := .call "f" [{ ty := .named "B", lvalue := true }] (.selected 2)
    source := "computed by Program.call" }

/-- `void f(A)` alone: the ambiguous conversion sequence keeps `f` viable,
and selecting it makes the call ill-formed. -/
def ambiguousSequenceSelected : Case :=
  { name := "ambiguous_sequence_selected"
    cite := cite "over.best.ics.general#12"
    program := [ .class "B", .class "A"
               , .converting (.named "A") (.constructor (.lref (.named "B")))
               , .converting (.named "B") (.function (.named "A") false false)
               , defaultedCtor (.named "A")
               , .function "f" [.named "A"] ]
    query := .call "f" [{ ty := .named "B", lvalue := true }] (.illFormed "the conversion of an argument is ambiguous")
    source := "computed by Program.call" }

/-- `struct S {}; struct T { constexpr T(const S&); }; template <T> void
f(); f<S{}>()`: the candidate initializer `constexpr T v = S{};` goes
through the converting constructor, and the parameter's value is the
object it makes. -/
def constructedValue : Case :=
  { name := "constructed_value"
    cite := cite "temp.arg.nontype#3"
    program := ctorProgram ++ [.functionTemplate (constTemplate cT)]
    query := .deduction "f" [] (some [(0, .value (.obj' "T" []))]) (explicit := [.value (.obj' "S" [])])
    source := "computed by deduceTemplate" }

/-- The same with the constructor explicit: the candidate initializer is
a copy-initialization, so the constructor is no candidate and the
template-id is invalid. -/
def explicitConstructedValue : Case :=
  { name := "explicit_constructed_value"
    cite := cite "over.match.copy#1"
    program := [ .class "S", .class "T", .converting cT (.constructor (.lref (.const cS)) true)
               , defaultedCtor cT, .functionTemplate (constTemplate cT) ]
    query := .deduction "f" [] none (explicit := [.value (.obj' "S" [])])
    source := "computed by deduceTemplate" }

/-- `struct T {}; struct S { constexpr operator T() const; }; template <T>
void f(); f<S{}>()`: through a conversion function. -/
def convertedValue : Case :=
  { name := "converted_value"
    cite := cite "temp.arg.nontype#3"
    program := [.class "T", .class "S", .converting cS (.function cT), .functionTemplate (constTemplate cT)]
    query := .deduction "f" [] (some [(0, .value (.obj' "T" []))]) (explicit := [.value (.obj' "S" [])])
    source := "computed by deduceTemplate" }

/-! ### Type categories and the structural traits -/

/-- A trait case: the model's answer, asserted against the `std::` trait. -/
private def traitCase (name : String) (c : String) (program : Program) (q : Trait) (as : List Ty) :
    Case :=
  { name, cite := cite c, program, query := .trait q as (program.trait q as == .ok true)
    source := "computed by Program.trait" }

/-- `struct A { int x; int& r; };`: a class with a scalar member and a
reference member, for the trait cases. -/
private def classA : Program :=
  [.class "A", .member (.named "A") { name := "x", ty := .named "int" }
  , .member (.named "A") { name := "r", ty := .lref (.named "int") }]

/-- `is_integral_v<const int>`: a primary category through `const`. -/
def traitIntegralConst : Case :=
  traitCase "trait_integral_const" "meta.unary.cat#3" [] .isIntegral [.const (.named "int")]

/-- `is_class_v<A>`, for a class with members. -/
def traitClass : Case := traitCase "trait_class" "meta.unary.cat#3" classA .isClass [.named "A"]

/-- `is_class_v<int>` is false: a fundamental type is no class. -/
def traitClassNotFundamental : Case :=
  traitCase "trait_class_not_fundamental" "meta.unary.cat#3" [] .isClass [.named "int"]

/-- `is_pointer_v<A* const>`. -/
def traitPointerConst : Case :=
  traitCase "trait_pointer_const" "meta.unary.cat#3" classA .isPointer [.const (.ptr (.named "A"))]

/-- `is_function_v<int(int, A&)>`. -/
def traitFunction : Case :=
  traitCase "trait_function" "meta.unary.cat#3" classA .isFunction
    [Ty.fn' [.named "int", .lref (.named "A")] (.named "int")]

/-- `is_lvalue_reference_v<A&>`. -/
def traitLvalueReference : Case :=
  traitCase "trait_lvalue_reference" "meta.unary.cat#3" classA .isLvalueReference [.lref (.named "A")]

/-- `is_rvalue_reference_v<int&>` is false: the categories are exclusive. -/
def traitRvalueReferenceOfLvalue : Case :=
  traitCase "trait_rvalue_reference_of_lvalue" "meta.unary.cat#3" [] .isRvalueReference
    [.lref (.named "int")]

/-- `is_void_v<const void>`. -/
def traitVoidConst : Case :=
  traitCase "trait_void_const" "meta.unary.cat#3" [] .isVoid [.const (.named "void")]

/-- `is_object_v<A&>` is false: a reference type is not an object type. -/
def traitReferenceNotObject : Case :=
  traitCase "trait_reference_not_object" "meta.unary.comp#2" classA .isObject [.lref (.named "A")]

/-- `is_object_v<int()>` is false: neither is a function type. -/
def traitFunctionNotObject : Case :=
  traitCase "trait_function_not_object" "meta.unary.comp#2" [] .isObject [Ty.fn' [] (.named "int")]

/-- `is_scalar_v<A*>`: a pointer is a scalar type. -/
def traitScalarPointer : Case :=
  traitCase "trait_scalar_pointer" "meta.unary.comp#2" classA .isScalar [.ptr (.named "A")]

/-- `is_compound_v<A>`: a class is a compound type. -/
def traitCompoundClass : Case :=
  traitCase "trait_compound_class" "meta.unary.comp#2" classA .isCompound [.named "A"]

/-- `is_fundamental_v<void>`. -/
def traitFundamentalVoid : Case :=
  traitCase "trait_fundamental_void" "meta.unary.comp#2" [] .isFundamental [.named "void"]

/-- `is_const_v<const int&>` is false: `is_const` is top-level only. -/
def traitConstReference : Case :=
  traitCase "trait_const_reference" "meta.unary.prop#5" [] .isConst [.lref (.const (.named "int"))]

/-- `is_same_v<int, const int>` is false: the same type with the same
cv-qualification. -/
def traitSameCv : Case :=
  traitCase "trait_same_cv" "meta.rel#3" [] .isSame [.named "int", .const (.named "int")]

/-- `is_same_v<C<int>, C<int>>`. -/
def traitSameSpecialization : Case :=
  traitCase "trait_same_specialization" "meta.rel#3" [.classTemplate "C" [{ kind := .type }]] .isSame
    [Ty.spec' "C" [.named "int"], Ty.spec' "C" [.named "int"]]

/-- `template <class T> requires std::is_class_v<T> void f(T);`: a trait
as an atomic constraint, answered by the model. -/
private def traitConstrained : FunctionTemplate :=
  { name := "f", head := [{ kind := .type }], params := [.param 0]
    constraint := some (.trait .isClass [.param 0]) }

/-- `f(A{})` selects the trait-constrained template. -/
def traitConstraintSelects : Case :=
  { name := "trait_constraint_selects"
    cite := cite "temp.constr.atomic#3.sentence-1"
    program := classA ++ [.functionTemplate traitConstrained]
    query := .call "f" [{ ty := .named "A" }] (.selected 0)
    source := "computed by Program.call" }

/-- `f(0)` finds no viable function: the trait constraint is not satisfied. -/
def traitConstraintExcludes : Case :=
  { name := "trait_constraint_excludes"
    cite := cite "temp.constr.atomic#3.sentence-1"
    program := classA ++ [.functionTemplate traitConstrained]
    query := .call "f" [{ ty := .named "int" }] .noMatch
    source := "computed by Program.call" }

/-! ### Special member functions, observed through a by-value parameter -/

private def cM : Ty := .named "M"
private def cX : Ty := .named "X"
/-- `void f(X);`, with `X` passed by value, and the lvalue and xvalue of `X`. -/
private def fX : Decl := .function "f" [cX]
private def xLvalue : CallArg := { ty := cX, lvalue := true }
private def xRvalue : CallArg := { ty := cX }
private def deletedCopy : String := "the copy-initialization of a parameter uses a deleted constructor"

/-- `struct M { M(const M&) = delete; }; struct X { M m; };`: `X`'s
defaulted copy constructor is defined as deleted, since resolution for
`M`'s copy selects a deleted constructor, so `f(x)` is ill-formed. -/
def deletedCopyPropagates : Case :=
  { name := "deleted_copy_propagates"
    cite := cite "class.copy.ctor#10"
    program := [ .class "M", .special cM { kind := .copyCtor, body := .deleted }
               , .class "X", .member cX { name := "m", ty := cM }, fX ]
    query := .call "f" [xLvalue] (.illFormed deletedCopy)
    source := "computed by Program.call" }

/-- The same `M` with `M(M&&) = default;`: `X`'s defaulted move
constructor selects `M`'s move, which is usable, so `f(X{})` moves and is
well-formed, while `f(x)` stays ill-formed. -/
def deletedCopyMoveRescues : Case :=
  { name := "deleted_copy_move_rescues"
    cite := cite "class.copy.ctor#10"
    program := [ .class "M", .special cM { kind := .copyCtor, body := .deleted }
               , .special cM { kind := .moveCtor, body := .defaulted, constParam := false }
               , .class "X", .member cX { name := "m", ty := cM }, fX ]
    query := .call "f" [xRvalue] (.selected 0)
    source := "computed by Program.call" }

/-- `struct M { M(const M&) = default; M(M&&) = delete; }; struct X { M m; };`:
`X`'s defaulted move constructor is defined as deleted and ignored by
overload resolution, so `f(X{})` copies and is well-formed. -/
def deletedDefaultedMoveIgnored : Case :=
  { name := "deleted_defaulted_move_ignored"
    cite := cite "class.copy.ctor#10"
    program := [ .class "M", .special cM { kind := .copyCtor, body := .defaulted }
               , .special cM { kind := .moveCtor, body := .deleted, constParam := false }
               , .class "X", .member cX { name := "m", ty := cM }, fX ]
    query := .call "f" [xRvalue] (.selected 0)
    source := "computed by Program.call" }

/-- `struct X { X(X&) {} };`: a copy constructor taking `X&` cannot copy a
`const X`, so `f(cx)` is ill-formed. -/
def nonConstCopyConstructor : Case :=
  { name := "non_const_copy_constructor"
    cite := cite "class.copy.ctor#1"
    program := [ .class "X", .special cX { kind := .copyCtor, constParam := false }, fX ]
    query := .call "f" [{ ty := .const cX, lvalue := true }] (.illFormed deletedCopy)
    source := "computed by Program.call" }

/-- `struct M { M(M&) {} }; struct X { M m; };`: `X`'s implicit copy
constructor has the form `X(X&)`, since `M`'s takes `M&`, so `f(cx)` is
ill-formed. -/
def copyConstructorFormNonConst : Case :=
  { name := "copy_constructor_form_non_const"
    cite := cite "class.copy.ctor#7"
    program := [ .class "M", .special cM { kind := .copyCtor, constParam := false }
               , .class "X", .member cX { name := "m", ty := cM }, fX ]
    query := .call "f" [{ ty := .const cX, lvalue := true }] (.illFormed deletedCopy)
    source := "computed by Program.call" }

/-- The same, with a non-const lvalue: `X(X&)` copies it. -/
def copyConstructorFormNonConstLvalue : Case :=
  { name := "copy_constructor_form_non_const_lvalue"
    cite := cite "class.copy.ctor#7"
    program := [ .class "M", .special cM { kind := .copyCtor, constParam := false }
               , .class "X", .member cX { name := "m", ty := cM }, fX ]
    query := .call "f" [xLvalue] (.selected 0)
    source := "computed by Program.call" }

/-- `struct X { int& r; };`: an lvalue reference member deletes the
default constructor and the assignments, not the copy constructor, so
`f(x)` copies. -/
def referenceMemberCopies : Case :=
  { name := "reference_member_copies"
    cite := cite "class.copy.ctor#10"
    program := [ .class "X", .member cX { name := "r", ty := .lref (.named "int") }, fX ]
    query := .call "f" [xLvalue] (.selected 0)
    source := "computed by Program.call" }

/-- `struct X { int&& r; };`: an rvalue reference member deletes the
defaulted copy constructor, so `f(x)` is ill-formed. -/
def rvalueReferenceMemberDeletesCopy : Case :=
  { name := "rvalue_reference_member_deletes_copy"
    cite := cite "class.copy.ctor#10"
    program := [ .class "X", .member cX { name := "r", ty := .rref (.named "int") }, fX ]
    query := .call "f" [xLvalue] (.illFormed deletedCopy)
    source := "computed by Program.call" }

/-- The same class moved: the move constructor is defaulted and not
deleted, so `f(X{})` is well-formed. -/
def rvalueReferenceMemberMoves : Case :=
  { name := "rvalue_reference_member_moves"
    cite := cite "class.copy.ctor#10"
    program := [ .class "X", .member cX { name := "r", ty := .rref (.named "int") }, fX ]
    query := .call "f" [xRvalue] (.selected 0)
    source := "computed by Program.call" }

/-! ### Traits answered by the program -/

private def cB : Ty := .named "B"
private def cD : Ty := .named "D"
/-- `struct B {}; struct D : B {};` -/
private def derivation : Program := [.class "B", .class "D" [cB]]
/-- `struct M { M(const M&) = delete; }; struct X { M m; };` -/
private def deletedMember : Program :=
  [ .class "M", .special cM { kind := .copyCtor, body := .deleted }
  , .class "X", .member cX { name := "m", ty := cM } ]
/-- `struct X { int& r; };` -/
private def refMember : Program := [.class "X", .member cX { name := "r", ty := .lref (.named "int") }]
/-- `struct X { const int c; };` -/
private def constMember : Program := [.class "X", .member cX { name := "c", ty := .const (.named "int") }]

def traitBaseOf : Case := traitCase "trait_base_of" "meta.rel#3" derivation .isBaseOf [cB, cD]
def traitBaseOfReversed : Case :=
  traitCase "trait_base_of_reversed" "meta.rel#3" derivation .isBaseOf [cD, cB]
def traitBaseOfSelf : Case := traitCase "trait_base_of_self" "meta.rel#3" derivation .isBaseOf [cB, cB]
def traitBaseOfScalar : Case :=
  traitCase "trait_base_of_scalar" "meta.rel#3" [] .isBaseOf [.named "int", .named "int"]

/-- `is_convertible_v<D, B>`: the derived-to-base copy. -/
def traitConvertibleToBase : Case :=
  traitCase "trait_convertible_to_base" "meta.rel#6" derivation .isConvertible [cD, cB]
def traitConvertibleToDerived : Case :=
  traitCase "trait_convertible_to_derived" "meta.rel#6" derivation .isConvertible [cB, cD]
/-- `is_convertible_v<S, T>` through a converting constructor, and not
through an explicit one. -/
def traitConvertibleConstructor : Case :=
  traitCase "trait_convertible_constructor" "meta.rel#6"
    [.class "S", .class "T", .converting cT (.constructor (.lref (.const cS)))] .isConvertible [cS, cT]
def traitConvertibleExplicit : Case :=
  traitCase "trait_convertible_explicit" "meta.rel#6"
    [.class "S", .class "T", .converting cT (.constructor (.lref (.const cS)) true)] .isConvertible [cS, cT]
/-- `is_convertible_v<X, X>` with a deleted copy constructor and no move:
the copy that the return performs is deleted. -/
def traitConvertibleDeletedCopy : Case :=
  traitCase "trait_convertible_deleted_copy" "meta.rel#6" deletedMember .isConvertible [cX, cX]

/-- `is_copy_constructible_v<X>` where `X` holds an `M` whose copy
constructor is deleted. -/
def traitCopyConstructibleDeleted : Case :=
  traitCase "trait_copy_constructible_deleted" "meta.unary.prop#5" deletedMember .isCopyConstructible [cX]
def traitMoveConstructibleDeleted : Case :=
  traitCase "trait_move_constructible_deleted" "meta.unary.prop#5" deletedMember .isMoveConstructible [cX]
/-- `is_default_constructible_v<X>` with a reference member, and with a
`const` member. -/
def traitDefaultConstructibleReference : Case :=
  traitCase "trait_default_constructible_reference" "meta.unary.prop#5" refMember
    .isDefaultConstructible [cX]
def traitDefaultConstructibleConst : Case :=
  traitCase "trait_default_constructible_const" "meta.unary.prop#5" constMember
    .isDefaultConstructible [cX]
/-- `is_constructible_v<X, const X&>` and `is_constructible_v<T, const S&>`. -/
def traitConstructibleCopy : Case :=
  traitCase "trait_constructible_copy" "meta.unary.prop#9" refMember .isConstructible [cX, .lref (.const cX)]
def traitConstructibleConverting : Case :=
  traitCase "trait_constructible_converting" "meta.unary.prop#9"
    [.class "S", .class "T", .converting cT (.constructor (.lref (.const cS)) true)] .isConstructible
    [cT, .lref (.const cS)]

/-- `is_copy_assignable_v<X>` with a reference member, and with a `const`
member; `is_move_assignable_v` likewise. -/
def traitCopyAssignableReference : Case :=
  traitCase "trait_copy_assignable_reference" "meta.unary.prop#5" refMember .isCopyAssignable [cX]
def traitMoveAssignableConst : Case :=
  traitCase "trait_move_assignable_const" "meta.unary.prop#5" constMember .isMoveAssignable [cX]
def traitCopyAssignablePlain : Case :=
  traitCase "trait_copy_assignable_plain" "meta.unary.prop#5" classA .isCopyAssignable [.named "A"]
/-- `is_assignable_v<X&, const X&>` and `<const X&, X>`. -/
def traitAssignableConstObject : Case :=
  traitCase "trait_assignable_const_object" "meta.unary.prop#5" derivation .isAssignable
    [.lref (.const cB), cB]

/-- `is_destructible_v<X>` with `~X() = delete;`, and through a member. -/
def traitDestructibleDeleted : Case :=
  traitCase "trait_destructible_deleted" "meta.unary.prop#5"
    [.class "X", .special cX { kind := .dtor, body := .deleted }] .isDestructible [cX]
def traitDestructibleMember : Case :=
  traitCase "trait_destructible_member" "meta.unary.prop#5"
    [ .class "M", .special cM { kind := .dtor, body := .deleted }
    , .class "X", .member cX { name := "m", ty := cM } ] .isDestructible [cX]

/-- `is_trivially_copyable_v`: a flat class is; a user-provided copy
constructor is not; a deleted copy constructor beside a defaulted move
constructor still is, since the move constructor is the one eligible
copy or move member and it is trivial. -/
def traitTriviallyCopyableFlat : Case :=
  traitCase "trait_trivially_copyable_flat" "class.prop#1" classA .isTriviallyCopyable [.named "A"]
def traitTriviallyCopyableUserProvided : Case :=
  traitCase "trait_trivially_copyable_user_provided" "class.prop#1"
    [.class "X", .special cX { kind := .copyCtor }] .isTriviallyCopyable [cX]
def traitTriviallyCopyableDeletedCopy : Case :=
  traitCase "trait_trivially_copyable_deleted_copy" "class.prop#1"
    [ .class "X", .special cX { kind := .copyCtor, body := .deleted }
    , .special cX { kind := .moveCtor, body := .defaulted, constParam := false } ] .isTriviallyCopyable [cX]
def traitTriviallyCopyableScalar : Case :=
  traitCase "trait_trivially_copyable_scalar" "basic.types.general#7" [] .isTriviallyCopyable
    [.ptr (.named "int")]

/-- `is_standard_layout_v`: a reference member breaks it; members in
both a base and the derived class break it; two subobjects of one base
class break it; a derived class with the members all in one class keeps
it. -/
def traitStandardLayoutReference : Case :=
  traitCase "trait_standard_layout_reference" "class.prop#2" refMember .isStandardLayout [cX]
def traitStandardLayoutTwoClasses : Case :=
  traitCase "trait_standard_layout_two_classes" "class.prop#2"
    [ .class "B", .member cB { name := "b", ty := .named "int" }
    , .class "D" [cB], .member cD { name := "d", ty := .named "int" } ] .isStandardLayout [cD]
def traitStandardLayoutRepeatedBase : Case :=
  traitCase "trait_standard_layout_repeated_base" "class.prop#2"
    [ .class "Q", .class "S" [.named "Q"], .class "T" [.named "Q"], .class "U" [.named "S", .named "T"] ]
    .isStandardLayout [.named "U"]
def traitStandardLayoutDerived : Case :=
  traitCase "trait_standard_layout_derived" "class.prop#2"
    [ .class "B", .member cB { name := "b", ty := .named "int" }, .class "D" [cB] ] .isStandardLayout [cD]
/-- `is_standard_layout_v<D>` where `D : B` has a first member of type `B`:
a base among the types at offset zero. -/
def traitStandardLayoutZeroOffset : Case :=
  traitCase "trait_standard_layout_zero_offset" "class.prop#2"
    [ .class "B", .class "D" [cB], .member cD { name := "b", ty := cB } ] .isStandardLayout [cD]

/-- `is_empty_v`: no members and empty bases; a base with a member
breaks it. -/
def traitEmpty : Case := traitCase "trait_empty" "meta.unary.prop#5" derivation .isEmpty [cD]
def traitEmptyBaseMember : Case :=
  traitCase "trait_empty_base_member" "meta.unary.prop#5"
    [ .class "B", .member cB { name := "b", ty := .named "int" }, .class "D" [cB] ] .isEmpty [cD]

/-- `is_trivially_default_constructible_v`: a default member initializer
breaks it; `is_trivially_copy_constructible_v` of a user-provided copy
constructor is false; `is_trivially_destructible_v` of a user-provided
destructor is false, of a flat class true. -/
def traitTriviallyDefaultConstructibleInit : Case :=
  traitCase "trait_trivially_default_constructible_init" "class.default.ctor#3"
    [.class "X", .member cX { name := "x", ty := .named "int", init := true }]
    .isTriviallyDefaultConstructible [cX]
def traitTriviallyCopyConstructibleUserProvided : Case :=
  traitCase "trait_trivially_copy_constructible_user_provided" "class.copy.ctor#12"
    [ .class "M", .special cM { kind := .copyCtor }, .class "X", .member cX { name := "m", ty := cM } ]
    .isTriviallyCopyConstructible [cX]
def traitTriviallyDestructibleUserProvided : Case :=
  traitCase "trait_trivially_destructible_user_provided" "class.dtor#8"
    [ .class "M", .special cM { kind := .dtor }, .class "X", .member cX { name := "m", ty := cM } ]
    .isTriviallyDestructible [cX]
def traitTriviallyDestructibleFlat : Case :=
  traitCase "trait_trivially_destructible_flat" "class.dtor#8" classA .isTriviallyDestructible [.named "A"]
def traitTriviallyMoveAssignableFlat : Case :=
  traitCase "trait_trivially_move_assignable_flat" "class.copy.assign#9" classA
    .isTriviallyMoveAssignable [.named "A"]

/-- `is_invocable_v<int(int, const A&), int, A>` and with a missing
argument. -/
def traitInvocableFunction : Case :=
  traitCase "trait_invocable_function" "meta.rel#3" classA .isInvocable
    [Ty.fn' [.named "int", .lref (.const (.named "A"))] (.named "int"), .named "int", .named "A"]
def traitInvocableArity : Case :=
  traitCase "trait_invocable_arity" "meta.rel#3" classA .isInvocable
    [Ty.fn' [.named "int", .lref (.const (.named "A"))] (.named "int"), .named "int"]

/-- A trait the program answers, in a requires-clause:
`template <class T> requires std::is_copy_constructible_v<T> void f(T);`
at a class with a deleted copy constructor. -/
def traitConstraintCopyConstructible : Case :=
  { name := "trait_constraint_copy_constructible"
    cite := cite "temp.constr.atomic#3.sentence-1"
    program := deletedMember ++
      [.functionTemplate { name := "f", head := [{ kind := .type }], params := [.lref (.const (.param 0))]
                           constraint := some (.trait .isCopyConstructible [.param 0]) }]
    query := .call "f" [{ ty := cX, lvalue := true }] .noMatch
    source := "computed by Program.call" }

/-- Every case of the Standard side. -/
def cases : List Case :=
  [ draftDeductCall3_rvalue, draftDeductCall3_lvalue, forwardingLvalue, forwardingRvalue
  , specialization, pointerMismatch, inconsistent, nonTemplatePreferred, redeclarationNotOverload
  , innerHidesOuter, innerSelected, outerAtGlobal, parentFound, nearestEnclosing, nothingFound
  , argdepExample, freeFunctionAdmitsAdl, adlThroughBase, adlThroughTemplateArgument
  , noAdlForFundamental, derivedHidesBase, baseMemberFound, ambiguousBases, objectCall
  , objectSuppressesAdl, dependentFindsLater, dependentBoundAtDefinition
  , dependentInstantiationContext, dependentReferencePoint
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
  , dispatchIfConstexprHard, protectedBaseSelected, protectedBaseDeduced, publicBaseSelected
  , draftDeductGeneral12_narrowing, draftDeductGeneral12_ambiguous, boolNarrowing, boolConverted
  , unsignedNarrowing, boolPromoted, intToLong, derivedToBaseValue
  , userConversionSelected, userConversionLosesRank, conversionFunctionSelected
  , convertedTemporaryBinds, convertedTemporaryRefused, explicitConstructorNotCandidate
  , secondSequenceDecides, conversionChainStops, draftBestIcsAmbiguous, draftBestIcsResolved
  , ambiguousSequenceSelected, constructedValue, explicitConstructedValue, convertedValue
  , traitIntegralConst, traitClass, traitClassNotFundamental, traitPointerConst, traitFunction
  , traitLvalueReference, traitRvalueReferenceOfLvalue, traitVoidConst, traitReferenceNotObject
  , traitFunctionNotObject, traitScalarPointer, traitCompoundClass, traitFundamentalVoid
  , traitConstReference, traitSameCv, traitSameSpecialization, traitConstraintSelects
  , traitConstraintExcludes
  , deletedCopyPropagates, deletedCopyMoveRescues, deletedDefaultedMoveIgnored
  , nonConstCopyConstructor, copyConstructorFormNonConst, copyConstructorFormNonConstLvalue
  , referenceMemberCopies, rvalueReferenceMemberDeletesCopy, rvalueReferenceMemberMoves
  , traitBaseOf, traitBaseOfReversed, traitBaseOfSelf, traitBaseOfScalar, traitConvertibleToBase
  , traitConvertibleToDerived, traitConvertibleConstructor, traitConvertibleExplicit
  , traitConvertibleDeletedCopy, traitCopyConstructibleDeleted, traitMoveConstructibleDeleted
  , traitDefaultConstructibleReference, traitDefaultConstructibleConst, traitConstructibleCopy
  , traitConstructibleConverting, traitCopyAssignableReference, traitMoveAssignableConst
  , traitCopyAssignablePlain, traitAssignableConstObject, traitDestructibleDeleted
  , traitDestructibleMember, traitTriviallyCopyableFlat, traitTriviallyCopyableUserProvided
  , traitTriviallyCopyableDeletedCopy, traitTriviallyCopyableScalar, traitStandardLayoutReference
  , traitStandardLayoutTwoClasses, traitStandardLayoutRepeatedBase, traitStandardLayoutDerived
  , traitStandardLayoutZeroOffset, traitEmpty, traitEmptyBaseMember
  , traitTriviallyDefaultConstructibleInit, traitTriviallyCopyConstructibleUserProvided
  , traitTriviallyDestructibleUserProvided, traitTriviallyDestructibleFlat
  , traitTriviallyMoveAssignableFlat, traitInvocableFunction, traitInvocableArity
  , traitConstraintCopyConstructible ]

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
  | .call callee as _ explicit scope =>
    some ((c.program.callAt (envOf c.program c.atomics) c.program.length scope callee as explicit).map
      (·.index))
  | .memberCall cls callee as _ explicit =>
    some ((c.program.memberCallAt (envOf c.program c.atomics) c.program.length cls callee as
      explicit).map (·.index))
  | .dependentCall pos _ =>
    match c.program[pos]? with
    | some (.dependentCall callee as s) =>
      some ((c.program.dependentCallAt (envOf c.program c.atomics) pos s callee as).map (·.index))
    | _ => none
  | _ => none

/-- The Standard side's cases are computed in the program's own
environment. -/
def computed (c : Case) : Option (Option (List (ParamIdx × Ty))) :=
  computedWith (fun p a => Env.ofProgram p a) c

def computedCall (c : Case) : Option (Resolution Nat) :=
  computedCallWith (fun p a => Env.ofProgram p a) c

/-- For a trait case, what the model computes: the trait's answer, which
is never a hard error, read as a constraint reads it. -/
def computedTrait (c : Case) : Option Bool :=
  match c.query with
  | .trait tr as _ => some (c.program.trait tr as == .ok true)
  | _ => none

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
