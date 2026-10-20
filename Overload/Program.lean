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
  /-- A non-template function, by name and parameter types. -/
  | function (name : String) (params : List Ty) (scope : Scope := [])
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
  model sees the concept only as an atomic constraint by name. -/
  | concept (name : String) (body : String)
  /-- A dependent call `callee(args)` written in a template defined at
  this position, instantiated with these argument types: its name is
  looked up in the definition context here and in the instantiation
  context at the unit's end ([temp.dep.general]/2). -/
  | dependentCall (callee : String) (args : List CallArg) (scope : Scope := [])
  deriving Repr, DecidableEq, Inhabited

attribute [std rule "temp.dep.general#2"] Decl.dependentCall

/-- A program: declarations in order. -/
abbrev Program := List Decl

namespace Program

/-- The declarations with a name, in order: the candidate set of a call. -/
def candidates (p : Program) (name : String) : List Decl :=
  p.filter fun
    | .function n _ _ => n = name
    | .functionTemplate ft => ft.name = name
    | _ => false

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

end Overload
