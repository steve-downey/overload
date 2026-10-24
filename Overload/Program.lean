-- Overload/Program.lean                                              -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Syntax
import Overload.Constraint

/-!
# Programs as data

A program is an ordered list of declarations, so declared-before-use is a
checkable predicate. The declarations are the ones the fragment needs:
classes and class templates, functions and function templates as the
candidates of a call, and a variable template with its partial
specializations. The model calls the variable template a lookup and its
partial specializations instances, after the use it was built for.

Name lookup is out of scope: the candidate set of a call is the
declarations with the callee's name, in order.
-/

namespace Overload

/-- The kind of a template parameter. -/
inductive ParamKind where
  /-- `class T`. -/
  | type
  /-- A constant template parameter of the given type; `const auto&` is
  `.const (.lref (.const (.named "auto")))`, with the placeholder as a
  name. -/
  | const (ty : Ty)
  deriving Repr, DecidableEq, Inhabited

/-- One entry of a template head. -/
structure TemplateParam where
  kind : ParamKind
  /-- The default template argument, which may mention preceding
  parameters. -/
  default : Option Ty := none
  deriving Repr, DecidableEq, Inhabited

/-- A template head: the parameters, by position. -/
abbrev Head := List TemplateParam

/-- One step of a scope path: a namespace or a class, each introduced by
a declaration in the enclosing scope ([basic.scope.scope]/1). -/
inductive ScopeStep where
  /-- `namespace name { ... }`. -/
  | «namespace» (name : String)
  /-- The scope of the class `name`. -/
  | «class» (name : String)
  deriving Repr, DecidableEq, Inhabited

/-- A scope, as the path from the global scope inward: `[]` is the global
scope, `[.namespace "a", .namespace "b"]` is `a::b`. The decision is
`decisions.md#scope-syntax`: a scope is a field of each namespace-scope
declaration, and the program stays a flat list. -/
abbrev Scope := List ScopeStep

/-- A function template: what [temp.deduct.general] deduces for. -/
structure FunctionTemplate where
  name : String
  head : Head
  /-- The function parameter types, in terms of the head's parameters. -/
  params : List Ty
  /-- How many trailing function parameters have default arguments. -/
  defaultArgs : Nat := 0
  /-- The return type. -/
  ret : Ty := .named "void"
  /-- The associated constraints. -/
  constraint : Option Constraint := none
  /-- The Mandates: a condition in the body, `static_assert` in the
  library's wording, checked only once overload resolution has selected
  the specialization and its definition is instantiated. -/
  mandate : Option Constraint := none
  /-- The scope the template inhabits. -/
  scope : Scope := []
  deriving Repr, DecidableEq, Inhabited

/-- The context an initialization runs in: argument passing, a function
return and the `=` form are copy-initialization; a parenthesized
initializer, a cast and functional notation are direct-initialization.
The fragment has only the first, so `direct` is the contrast that admits
explicit candidates. -/
inductive Init where
  /-- Copy-initialization ([dcl.init.general]/13). -/
  | copy
  /-- Direct-initialization ([dcl.init.general]/14). -/
  | direct
  deriving Repr, DecidableEq, Inhabited

attribute [std rule "dcl.init.general#13"] Init.copy
attribute [std rule "dcl.init.general#14"] Init.direct

/-- A user-defined conversion declared for a class: a converting
constructor, by the type of its one parameter, or a conversion function,
by the type it converts to. Either may be explicit, in which case it is
a candidate only for direct-initialization. The fragment has no
expressions, so a conversion is its declaration: what it converts from
and to, and whether it is explicit
(`decisions.md#user-defined-conversions`). -/
inductive UserConv where
  /-- A constructor `cls(param)`, which specifies a conversion from
  `param` to `cls` when not explicit. -/
  | constructor (param : Ty) (explicit : Bool := false)
  /-- A conversion function `operator target()`, which specifies a
  conversion from its class to `target`; `const` when its implicit
  object parameter is a reference to const. -/
  | function (target : Ty) (explicit : Bool := false) (const : Bool := true)
  deriving Repr, DecidableEq, Inhabited

attribute [std rule "class.conv.ctor#1"] UserConv.constructor
attribute [std rule "class.conv.fct#2"] UserConv.function

/-- Is the conversion explicit? -/
def UserConv.explicit : UserConv → Bool
  | .constructor _ e | .function _ e _ => e

/-- A non-static data member of a class: its name, its type, and whether
it has a default member initializer. The initializer is an expression,
so the model keeps only that there is one. -/
@[std rule "class.mem.general#5" "class.mem.general#15"]
structure Member where
  name : String
  ty : Ty
  init : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- The kinds of special member function: default constructor, copy and
move constructor, copy and move assignment operator, destructor. -/
@[std rule "special#1"]
inductive SmfKind where
  | defaultCtor | copyCtor | moveCtor | copyAssign | moveAssign | dtor
  deriving Repr, DecidableEq, Inhabited

/-- Is the kind a constructor's? -/
def SmfKind.isCtor : SmfKind → Bool
  | .defaultCtor | .copyCtor | .moveCtor => true
  | _ => false

/-- Is the kind an assignment operator's? -/
def SmfKind.isAssign : SmfKind → Bool
  | .copyAssign | .moveAssign => true
  | _ => false

/-- How a user-declared special member function is defined on its first
declaration: with a body, `= default`, or `= delete`. -/
inductive SmfBody where
  | userProvided | defaulted | deleted
  deriving Repr, DecidableEq, Inhabited

attribute [std rule "dcl.fct.def.default#5"] SmfBody.userProvided
attribute [std rule "dcl.fct.def.default#1"] SmfBody.defaulted
attribute [std rule "dcl.fct.def.delete#1"] SmfBody.deleted

/-- How a member function is declared with respect to virtuality: with
no specifier; with `virtual`; with `virtual` and a pure-specifier, `= 0`;
with the virt-specifier `override`, which makes it virtual by overriding
and is ill-formed otherwise; or with the virt-specifier `final`, a
virtual function no derived class may override. A function at namespace
scope has no virtuality, and the judgements of `Overload/Virtual.lean`
look at member functions only. -/
inductive Virt where
  | none | virtual | pure | override | final
  deriving Repr, DecidableEq, Inhabited

attribute [std rule "class.virtual#1"] Virt.none Virt.virtual
attribute [std rule "class.abstract#2"] Virt.pure
attribute [std rule "class.virtual#5"] Virt.override
attribute [std rule "class.virtual#4"] Virt.final

/-- Is the function virtual by its own declaration, before any
overriding: first declared `virtual`, pure, or `final`? An `override`
is virtual only through the function it overrides. -/
@[std rule "class.virtual#1.sentence-1"]
def Virt.declared : Virt → Bool
  | .virtual | .pure | .final => true
  | .none | .override => false

/-- A user-declared special member function: its kind, its body, and
whether its parameter is a reference to `const` ([class.copy.ctor]/1,
[class.copy.assign]/1), which a default constructor and a destructor
ignore; a destructor may be declared virtual, pure, `override` or `final`
([class.dtor]/11), which the other kinds ignore. Every special member of
the fragment is public, unconstrained, and without an exception
specification. -/
@[std rule "class.dtor#11"]
structure SmfDecl where
  kind : SmfKind
  body : SmfBody := .userProvided
  constParam : Bool := true
  virt : Virt := .none
  deriving Repr, DecidableEq, Inhabited

/-- A semantic requirement: what the arguments of a concept must do,
beyond satisfying its constraint, to model it ([res.on.requirements]/1).
A slug names the question, kebab-case; the statement is the requirement
in words, which the Standard gives in prose about values and the model
has no expressions to evaluate. Nothing decides one: `Laws` is the oracle,
a hypothesis a theorem states (`decisions.md#semantic-requirements`). A
required operation need not be a total function, so a requirement is
stated on the domain of its expressions ([structure.requirements]/8). -/
@[std rule "res.on.requirements#1" "structure.requirements#8"]
structure Semantic where
  slug : String
  statement : String
  deriving Repr, DecidableEq, Inhabited

/-- A declaration. Every namespace-scope declaration carries the scope it
inhabits, defaulting to the global scope; a declaration whose scope ends
in a class step is a member of that class. -/
inductive Decl where
  /-- `struct name : public bases..., protected protectedBases... {};`.
  A base may be a class template specialization. -/
  | «class» (name : String) (bases : List Ty := []) (protectedBases : List Ty := [])
      (scope : Scope := [])
  /-- `template <head> struct name {};` -/
  | classTemplate (name : String) (head : Head) (scope : Scope := [])
  /-- A non-template function, by name and parameter types; a member
  function when its scope ends in a class step, and then with its
  virtuality ([class.virtual]/1). -/
  | function (name : String) (params : List Ty) (scope : Scope := []) (virt : Virt := .none)
  /-- A function template. -/
  | functionTemplate (ft : FunctionTemplate)
  /-- The primary of a lookup variable template, `trait<T>`, with a value
  of its own, `std::false_type`: the soft design. -/
  | lookup (name : String)
  /-- The primary of a lookup variable template whose default fails hard:
  a `static_assert` fires when it is instantiated for a type without an
  instance. The design the step-order probe tests. -/
  | lookupHard (name : String)
  /-- A partial specialization of a lookup variable template, an instance,
  for the types matching `pattern` under `head`. -/
  | instance (name : String) (head : Head) (pattern : Ty)
  /-- A point of the program that instantiates the lookup for a type. -/
  | use (name : String) (ty : Ty)
  /-- An object, `inline constexpr cls name{};`: an instance object
  declared outside lookup for a user to pin by name, or an operation
  object whose class has the call operators. -/
  | object (name : String) (cls : String := "pinned_instance") (scope : Scope := [])
  /-- `template <class T> concept name = body;`, for the emitted C++; the
  model sees the concept only as an atomic constraint by name. With
  `arity` two or more the parameters are `T0, T1, ...`. -/
  | concept (name : String) (body : String) (arity : Nat := 1)
  /-- A dependent call `callee(args)` written in a template defined at
  this position, instantiated with these argument types: its name is
  looked up in the definition context here and in the instantiation
  context, the point of instantiation of the specialization, which
  follows each declaration that refers to it and is the unit's end as
  well ([temp.dep.general]/2, [temp.point]/1, /7). -/
  | dependentCall (callee : String) (args : List CallArg) (scope : Scope := [])
  /-- A namespace-scope declaration that refers to the specialization of
  the template defined at `call`, a `dependentCall`, with the arguments
  it carries: the point of instantiation of the specialization
  immediately follows this declaration ([temp.point]/1). -/
  | refersTo (call : Nat)
  /-- A user-defined conversion of the class `cls`, a ground class type:
  a converting constructor or a conversion function declared in its
  definition. Its own declaration, after the class, so the program stays
  a flat list ([class.conv.general]/1). -/
  | converting (cls : Ty) (conv : UserConv)
  /-- A non-static data member of the class `cls`, a ground class type,
  declared in its definition. Its own declaration, after the class, as a
  conversion is, so the program stays a flat list. -/
  | member (cls : Ty) (m : Member)
  /-- A user-declared special member function of the class `cls`, a
  ground class type, declared in its definition. Its own declaration,
  after the class, like a conversion and a member. -/
  | special (cls : Ty) (s : SmfDecl)
  /-- `template <class T0, ...> concept name = body;`, with `arity` type
  parameters and a constraint for its body, whose parameters are
  `Ty.param i`. A concept-id `name<args>` normalizes to the body with the
  arguments substituted ([temp.constr.normal]/1). The string-bodied
  `concept` stays for the emitted C++ that the model reads as one atom. -/
  | conceptDef (name : String) (arity : Nat) (body : Constraint)
  /-- A semantic requirement given in the specification of the concept
  `concept`: its own declaration after the `conceptDef`, as a member is
  after its class. -/
  | semantic (concept : String) (law : Semantic)
  deriving Repr, DecidableEq, Inhabited

attribute [std rule "temp.dep.general#2"] Decl.dependentCall
attribute [std rule "temp.point#1.sentence-2"] Decl.refersTo
attribute [std rule "class.conv.general#1"] Decl.converting
attribute [std rule "class.mem.general#5"] Decl.member
attribute [std rule "special#1"] Decl.special
attribute [std rule "temp.constr.normal#1"] Decl.conceptDef
attribute [std rule "res.on.requirements#1"] Decl.semantic

/-- A program: declarations in order. -/
abbrev Program := List Decl

namespace Program

/-- The declarations with a name, in order: the candidate set of a call. -/
def candidates (p : Program) (name : String) : List Decl :=
  p.filter fun
    | .function n _ _ _ => n = name
    | .functionTemplate ft => ft.name = name
    | _ => false

/-- The non-static data members of a class, in declaration order. -/
def membersOf (p : Program) (c : Ty) : List Member :=
  p.filterMap fun
    | .member d m => if d == c then some m else none
    | _ => none

/-- The user-declared special member functions of a class, in order. -/
def specialDecls (p : Program) (c : Ty) : List SmfDecl :=
  p.filterMap fun
    | .special d s => if d == c then some s else none
    | _ => none

/-- The concept definition of a name, if any: its arity and body. -/
def conceptDef? (p : Program) (name : String) : Option (Nat × Constraint) :=
  p.findSome? fun
    | .conceptDef n a body => if n == name then some (a, body) else none
    | _ => none

/-- The semantic requirements the program gives in a concept's own
specification, in order. -/
def lawsOf (p : Program) (c : String) : List Semantic :=
  p.filterMap fun
    | .semantic n law => if n == c then some law else none
    | _ => none

/-- The first function template with a name, if any. -/
def functionTemplate? (p : Program) (name : String) : Option FunctionTemplate :=
  p.findSome? fun
    | .functionTemplate ft => if ft.name = name then some ft else none
    | _ => none

/-- Is the declaration an instance of `tc`? -/
def isInstanceOf (tc : String) : Decl → Bool
  | .instance c _ _ => c == tc
  | _ => false

/-- No partial specialization of a lookup is declared at or after a use of
it: every one a use could select is declared before it. -/
def declaredBeforeUse (p : Program) : Bool :=
  p.zipIdx.all fun (d, j) =>
    match d with
    | .use tc _ => !((p.drop j).any (isInstanceOf tc))
    | _ => true

end Program

/-- The standing assumption: one translation unit, with every instance
declared before any use that would instantiate its lookup. It hides the
real coherence hazards of C++, which are ill-formed with no diagnostic
required, and it is stated explicitly so that phase 8 can remove it.
Phase 8 shows it is exactly what keeps one unit free of a verdict
(`verdicts_single`). -/
@[assumed "single-tu"]
def SingleTranslationUnit (p : Program) : Prop :=
  p.declaredBeforeUse = true

instance (p : Program) : Decidable (SingleTranslationUnit p) :=
  inferInstanceAs (Decidable (_ = true))

/-! ## Constraint normalization -/

/-- Substitute a concept-id's arguments for the concept's parameters
throughout a constraint: in every mapping, and in the types of a
requires-expression. -/
def Constraint.substArgs (args : List Ty) : Constraint → Constraint :=
  let σ : Bindings := args.zipIdx.map fun (a, i) => (i, a)
  go σ
where
  go (σ : Bindings) : Constraint → Constraint
    | .atomic e m => .atomic e (m.map (Ty.subst σ))
    | .trait q m => .trait q (m.map (Ty.subst σ))
    | .requires reqs m => .requires (reqs.map (Constraint.Requirement.subst σ)) (m.map (Ty.subst σ))
    | .conceptId n as => .conceptId n (as.map (Ty.subst σ))
    | .conj l r => .conj (go σ l) (go σ r)
    | .disj l r => .disj (go σ l) (go σ r)

/-- The concept-ids a constraint names, with their arguments, outside any
requires-expression. -/
def Constraint.conceptIds : Constraint → List (String × List Ty)
  | .conceptId n as => [(n, as)]
  | .conj l r | .disj l r => l.conceptIds ++ r.conceptIds
  | _ => []

namespace Program

/-- The normal form of a constraint within `fuel` expansions: a
concept-id the program declares is replaced by the concept's body with
the arguments substituted into the parameter mappings of its atoms, and
normalized in turn; a conjunction or disjunction by the normal forms of
its operands; anything else is atomic with the identity mapping. A
concept names only concepts declared before it, so the program's length
bounds the expansion. -/
@[std rule "temp.constr.normal#1"]
def normalizeWithin (p : Program) : Nat → Constraint → Constraint
  | 0, c => c
  | fuel + 1, c => expand (fun d => p.normalizeWithin fuel d) c
where
  /-- Expand every concept-id of the constraint once, normalizing what
  each expands to with `next`. -/
  expand (next : Constraint → Constraint) : Constraint → Constraint
    | .conceptId n as =>
      match p.conceptDef? n with
      | some (_, body) => next (body.substArgs as)
      | none => .conceptId n as
    | .conj l r => .conj (expand next l) (expand next r)
    | .disj l r => .disj (expand next l) (expand next r)
    | c => c

/-- The normal form of a constraint. -/
def normalize (p : Program) (c : Constraint) : Constraint := p.normalizeWithin p.length c

/-- The semantic requirements modelling `c` needs, within `fuel`
expansions: those of `c`'s own specification, and those of every concept
its body is defined in terms of, since modelling `regular` is modelling
`semiregular` and `equality_comparable`. -/
@[std rule "res.on.requirements#1"]
def lawsWithin (p : Program) : Nat → String → List Semantic
  | 0, c => p.lawsOf c
  | fuel + 1, c =>
    p.lawsOf c ++
      match p.conceptDef? c with
      | some (_, body) => body.conceptIds.flatMap fun (n, _) => p.lawsWithin fuel n
      | none => []

/-- The semantic requirements modelling `c` needs, each once. -/
def laws (p : Program) (c : String) : List Semantic := (p.lawsWithin p.length c).eraseDups

/-- A declaration with its constraints normalized: the associated
constraints of a function template are the normal form of its
constraint-expression ([temp.constr.normal]/2). -/
@[std rule "temp.constr.normal#2"]
def normalizeDecl (p : Program) : Decl → Decl
  | .functionTemplate ft =>
    .functionTemplate { ft with constraint := ft.constraint.map p.normalize
                                mandate := ft.mandate.map p.normalize }
  | d => d

end Program

end Overload
