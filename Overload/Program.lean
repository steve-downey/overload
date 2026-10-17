-- Overload/Program.lean                                              -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Syntax
import Overload.Constraint

/-!
# Programs as data

A program is an ordered list of declarations, so declared-before-use is a
checkable predicate. The declarations are the ones the typeclass encoding
needs: classes and class templates for the types that take instances,
functions and function templates as the candidates of a call, and the
lookup variable template with its partial specializations, the instances.

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
  deriving Repr, DecidableEq, Inhabited

/-- A declaration. -/
inductive Decl where
  /-- `struct name : bases... {};`, with public bases, which may be class
  template specializations. -/
  | «class» (name : String) (bases : List Ty := [])
  /-- `template <head> struct name {};` -/
  | classTemplate (name : String) (head : Head)
  /-- A non-template function, by name and parameter types. -/
  | function (name : String) (params : List Ty)
  /-- A function template. -/
  | functionTemplate (ft : FunctionTemplate)
  /-- The primary of a lookup variable template, `functor<T>`, with the
  soft default instance, `std::false_type`. -/
  | lookup (typeclass : String)
  /-- The primary of a lookup variable template whose default fails hard:
  a `static_assert` fires when it is instantiated for a type without an
  instance. The design the step-order probe tests. -/
  | lookupHard (typeclass : String)
  /-- A partial specialization of a lookup variable template: an instance,
  for the types matching `pattern` under `head`. -/
  | instance (typeclass : String) (head : Head) (pattern : Ty)
  /-- A point of the program that instantiates the lookup for a type. -/
  | use (typeclass : String) (ty : Ty)
  /-- An instance object declared outside lookup, `inline constexpr
  pinned_instance name{};`, for a user to pin by name. -/
  | object (name : String)
  /-- `template <class T> concept name = body;`, for the emitted C++; the
  model sees the concept only as an atomic constraint by name. -/
  | concept (name : String) (body : String)
  deriving Repr, DecidableEq, Inhabited

/-- A program: declarations in order. -/
abbrev Program := List Decl

namespace Program

/-- The declarations with a name, in order: the candidate set of a call. -/
def candidates (p : Program) (name : String) : List Decl :=
  p.filter fun
    | .function n _ => n = name
    | .functionTemplate ft => ft.name = name
    | _ => false

/-- The first function template with a name, if any. -/
def functionTemplate? (p : Program) (name : String) : Option FunctionTemplate :=
  p.findSome? fun
    | .functionTemplate ft => if ft.name = name then some ft else none
    | _ => none

/-- The index of the first `use` of a typeclass's lookup, if any. -/
private def firstUse (p : Program) (tc : String) : Option Nat :=
  p.findIdx? fun
    | .use c _ => c = tc
    | _ => false

/-- The index of the last instance declared for a typeclass, if any. -/
private def lastInstance (p : Program) (tc : String) : Option Nat :=
  let idxs := p.zipIdx.filterMap fun (d, i) =>
    match d with
    | .instance c _ _ => if c = tc then some i else none
    | _ => none
  idxs.getLast?

/-- Every instance of every typeclass is declared before any use that
would instantiate its lookup. -/
def declaredBeforeUse (p : Program) : Bool :=
  let typeclasses := p.filterMap fun
    | .lookup c | .lookupHard c => some c
    | _ => none
  typeclasses.all fun tc =>
    match lastInstance p tc, firstUse p tc with
    | some i, some u => i < u
    | _, _ => true

end Program

/-- The standing assumption: one translation unit, with every instance
declared before any use that would instantiate its lookup. It hides the
real coherence hazards of C++, which are ill-formed with no diagnostic
required, and it is stated explicitly so that phase 8 can remove it. -/
@[assumed "single-tu"]
def SingleTranslationUnit (p : Program) : Prop :=
  p.declaredBeforeUse = true

instance (p : Program) : Decidable (SingleTranslationUnit p) :=
  inferInstanceAs (Decidable (_ = true))

end Overload
