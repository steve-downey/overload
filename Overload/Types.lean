-- Overload/Types.lean                                                -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Syntax
import Overload.Outcome

/-!
# Type categories

The categories of [basic.types] on the fragment's types, the integer
types with their ranges, and the structural type traits as queries a
constraint can state. A type describes an object, a reference or a
function ([basic.types.general]/1); exactly one primary category holds
of any type ([meta.unary.cat]/3), which `primary_category_unique`
proves of the fragment's concrete types.

The traits here need no program: whether a name is a class is whether
it is not a fundamental type, and the fragment's fundamental types are
its integer types and `void`. Traits that ask about a class's members or
special member functions come in later stages and are answered by the
program.
-/

namespace Overload

/-! ## Integer types -/

/-- The integer types of the fragment, by name, with the least and
greatest value each represents. The widths are the `integer-widths`
decision: LP64, `char` signed, and `bool` an integer type with range 0
to 1. -/
@[assumed "integer-widths", std rule "basic.fundamental#4"]
def integerTypes : List (String × Int × Int) :=
  [ ("bool", 0, 1)
  , ("char", -128, 127), ("signed char", -128, 127), ("unsigned char", 0, 255)
  , ("short", -32768, 32767), ("unsigned short", 0, 65535)
  , ("int", -2147483648, 2147483647)
  , ("unsigned", 0, 4294967295), ("unsigned int", 0, 4294967295)
  , ("long", -9223372036854775808, 9223372036854775807)
  , ("unsigned long", 0, 18446744073709551615)
  , ("long long", -9223372036854775808, 9223372036854775807)
  , ("unsigned long long", 0, 18446744073709551615) ]

/-- The range of an integer type, by name; `none` for any other name. -/
def integerRange (n : String) : Option (Int × Int) :=
  (integerTypes.find? (·.1 = n)).map (·.2)

/-- Is the name an integer type of the fragment? -/
def isInteger (n : String) : Bool := (integerRange n).isSome

/-- Whether an integer type represents a value: the value lies in the
type's range of representable values. -/
@[std rule "basic.fundamental#1"]
def representable (n : String) (v : Int) : Option Bool :=
  match integerRange n with
  | some (lo, hi) => some (decide (lo ≤ v ∧ v ≤ hi))
  | none => none

/-- The fundamental types of the fragment, by name: the integer types
and `void`. -/
def fundamentalName (n : String) : Bool := isInteger n || n == "void"

/-- The primary type categories of the fragment ([meta.unary.cat]/3):
the categories with an inhabitant among its types. Enumerations, unions,
arrays, floating-point types, `nullptr_t` and pointers to members have
none, and their traits answer `false`. -/
inductive Ty.Category where
  | void | integral | pointer | lvalueReference | rvalueReference | «class» | function
  deriving Repr, DecidableEq, Inhabited

namespace Ty

/-- A function type from a parameter list. -/
def fn' (ps : List Ty) (r : Ty) : Ty := .fn (args ps) r

/-- A ground type the fragment can spell: names, `const` on an object
type, pointers, references, specializations with concrete arguments,
function types. No template parameter, placeholder, synthesized type or
construct that forming computes; no `const` on a reference, a function
type or a `const` type, which forming never produces. -/
def concrete : Ty → Bool
  | .named n => n != "auto"
  | .const t => concrete t && !t.isRef && !(t matches .fn _ _) && !(t matches .const _)
  | .ptr t | .lref t | .rref t => concrete t
  | .spec c as => c != "auto" && concrete as
  | .fn ps r => concrete ps && concrete r
  | .nil => true
  | .cons a as => concrete a && concrete as
  | .value v => !v.dependent
  | _ => false

/-! ### The primary categories

Each is asked of the type with its top-level `const` removed, since a
category gives the same answer for `T` and cv `T` ([meta.unary.cat]/2). -/

/-- cv `void`. -/
def isVoid (t : Ty) : Bool := t.stripConst == .named "void"

/-- An integral type: one of the fragment's integer types. -/
def isIntegral (t : Ty) : Bool :=
  match t.stripConst with
  | .named n => isInteger n
  | _ => false

/-- A pointer type. -/
def isPointer (t : Ty) : Bool := t.stripConst matches .ptr _

/-- An lvalue reference type. -/
def isLvalueReference (t : Ty) : Bool := t matches .lref _

/-- An rvalue reference type. -/
def isRvalueReference (t : Ty) : Bool := t matches .rref _

/-- A class type: a named type that is not fundamental, or a class
template specialization. Every class of the fragment is non-union. -/
def isClass (t : Ty) : Bool :=
  match t.stripConst with
  | .named n => !fundamentalName n && n != "auto"
  | .spec c _ => c != "auto"
  | _ => false

/-- A function type ([basic.compound]/1). -/
@[std rule "basic.compound#1"]
def isFunction (t : Ty) : Bool := t matches .fn _ _

theorem isClass_not_void (t : Ty) (h : t.stripConst.isClass = true) : t.isVoid = false := by
  unfold Ty.isVoid
  cases hs : t.stripConst with
  | named n =>
    simp only [Ty.isClass] at h
    rw [hs] at h
    simp only [Ty.stripConst] at h
    by_cases hv : n = "void"
    · subst hv; simp [fundamentalName] at h
    · simp [hv]
  | _ => simp only [Ty.isClass] at h; rw [hs] at h; simp_all [Ty.stripConst]

theorem isClass_not_function (t : Ty) (h : t.stripConst.isClass = true) : t.isFunction = false := by
  cases t <;> simp_all [Ty.isFunction, Ty.isClass, Ty.stripConst]

theorem referred_isClass_not_void (t : Ty) (h : t.referred.stripConst.isClass = true) :
    t.isVoid = false := by
  cases t with
  | lref u | rref u => simp [Ty.isVoid, Ty.stripConst]
  | _ => exact isClass_not_void _ (by simpa [Ty.referred] using h)

theorem referred_isClass_not_function (t : Ty) (h : t.referred.stripConst.isClass = true) :
    t.isFunction = false := by
  cases t <;> simp_all [Ty.isFunction, Ty.isClass, Ty.stripConst, Ty.referred]

/-! ### The composite categories -/

/-- A reference type, lvalue or rvalue. -/
def isReference (t : Ty) : Bool := t.isLvalueReference || t.isRvalueReference

/-- An object type: a type that is not a function type, not a reference
type, and not cv `void`. -/
@[std rule "basic.types.general#6"]
def isObject (t : Ty) : Bool := t.isType && !t.isFunction && !t.isReference && !t.isVoid

/-- A scalar type: the fragment's are its arithmetic types, which are
its integer types, and its pointer types, cv-qualified or not. -/
@[std rule "basic.types.general#7"]
def isScalar (t : Ty) : Bool := t.isIntegral || t.isPointer

/-- A fundamental type: an integer type or `void`, cv-qualified or not. -/
def isFundamental (t : Ty) : Bool := t.isIntegral || t.isVoid

/-- A compound type: a concrete type that is not fundamental. The
fragment's compound types are pointers, references, classes and
functions ([basic.compound]/1). -/
@[std rule "basic.compound#1"]
def isCompound (t : Ty) : Bool := t.concrete && t.isType && !t.isFundamental

/-- Const-qualified at the top level: `const int` is, `const int&` and
`const int*` are not. -/
def isConst (t : Ty) : Bool := t matches .const _

/-! ### Transformations -/

/-- `std::remove_const_t`: the type without its top-level `const`. -/
def removeConst (t : Ty) : Ty := t.stripConst

/-- `std::remove_reference_t`: the referred type of a reference, the
type itself otherwise. -/
def removeReference (t : Ty) : Ty := t.referred

/-- `std::remove_cvref_t`. The constructor `Ty.removeCvref` is the alias
unresolved, in a non-deduced context; this is its value once the type
is known. -/
def stripCvref (t : Ty) : Ty := t.referred.stripConst

/-- `std::add_lvalue_reference_t`: an lvalue reference to the type, with
reference collapsing; a function type or `void` is left as it is, since
neither is referenceable in the fragment's spelling. -/
def addLvalueReference (t : Ty) : Ty :=
  if t.isFunction || t.isVoid then t else Ty.collapse (.lref t)

/-! ### Exactly one primary category -/

/-- The one primary category of a concrete type, by its form. -/
def primaryCategory (t : Ty) : Option Ty.Category :=
  match t.stripConst with
  | .named n =>
    if n == "void" then some .void
    else if isInteger n then some .integral
    else if n == "auto" then none
    else some .class
  | .ptr _ => some .pointer
  | .lref _ => some .lvalueReference
  | .rref _ => some .rvalueReference
  | .spec c _ => if c == "auto" then none else some .class
  | .fn _ _ => some .function
  | _ => none

end Ty

/-- The predicate of a primary category. -/
def Ty.Category.holds : Ty.Category → Ty → Bool
  | .void => Ty.isVoid
  | .integral => Ty.isIntegral
  | .pointer => Ty.isPointer
  | .lvalueReference => Ty.isLvalueReference
  | .rvalueReference => Ty.isRvalueReference
  | .class => Ty.isClass
  | .function => Ty.isFunction

theorem isInteger_void : isInteger "void" = false := by decide
theorem isInteger_auto : isInteger "auto" = false := by decide

/-- Exactly one primary category holds of a concrete type: a category
holds of `t` iff it is `t`'s primary category. -/
@[std theorem "meta.unary.cat#3"]
theorem primary_category_unique (t : Ty) (ht : t.concrete = true) (hty : t.isType = true)
    (c : Ty.Category) : c.holds t = true ↔ t.primaryCategory = some c := by
  cases t with
  | const t =>
    cases t with
    | named n =>
      cases c <;> simp [Ty.Category.holds, Ty.primaryCategory, Ty.isVoid, Ty.isIntegral, Ty.isPointer,
        Ty.isLvalueReference, Ty.isRvalueReference, Ty.isClass, Ty.isFunction, Ty.stripConst,
        fundamentalName] <;>
      by_cases hv : n = "void" <;> by_cases hi : isInteger n = true <;>
      by_cases ha : n = "auto" <;> simp_all [isInteger_void, isInteger_auto]
    | spec d as =>
      cases c <;> simp [Ty.Category.holds, Ty.primaryCategory, Ty.isVoid, Ty.isIntegral, Ty.isPointer,
        Ty.isLvalueReference, Ty.isRvalueReference, Ty.isClass, Ty.isFunction, Ty.stripConst] <;>
      by_cases ha : d = "auto" <;> simp_all
    | _ =>
      cases c <;> simp_all [Ty.Category.holds, Ty.primaryCategory, Ty.isVoid, Ty.isIntegral,
        Ty.isPointer, Ty.isLvalueReference, Ty.isRvalueReference, Ty.isClass, Ty.isFunction,
        Ty.stripConst, Ty.concrete, Ty.isType, Ty.isRef]
  | named n =>
    cases c <;> simp [Ty.Category.holds, Ty.primaryCategory, Ty.isVoid, Ty.isIntegral, Ty.isPointer,
      Ty.isLvalueReference, Ty.isRvalueReference, Ty.isClass, Ty.isFunction, Ty.stripConst,
      fundamentalName] <;>
    by_cases hv : n = "void" <;> by_cases hi : isInteger n = true <;>
    by_cases ha : n = "auto" <;> simp_all [isInteger_void, isInteger_auto]
  | spec d as =>
    cases c <;> simp [Ty.Category.holds, Ty.primaryCategory, Ty.isVoid, Ty.isIntegral, Ty.isPointer,
      Ty.isLvalueReference, Ty.isRvalueReference, Ty.isClass, Ty.isFunction, Ty.stripConst] <;>
    by_cases ha : d = "auto" <;> simp_all
  | _ =>
    cases c <;> simp_all [Ty.Category.holds, Ty.primaryCategory, Ty.isVoid, Ty.isIntegral,
      Ty.isPointer, Ty.isLvalueReference, Ty.isRvalueReference, Ty.isClass, Ty.isFunction,
      Ty.stripConst, Ty.concrete, Ty.isType]

/-! ## Traits as queries -/

/-- A type trait the fragment can state as a judgement. The structural
ones, the primary and composite categories, `is_const` and `is_same`,
are answered by `Trait.answer` from the types alone; the rest ask about
a program's classes and are answered by `Program.trait`
(`Overload/Traits.lean`). -/
inductive Trait where
  | isVoid | isIntegral | isPointer | isLvalueReference | isRvalueReference | isClass | isFunction
  | isReference | isObject | isScalar | isCompound | isFundamental
  | isConst
  | isSame
  | isBaseOf | isConvertible
  | isConstructible | isDefaultConstructible | isCopyConstructible | isMoveConstructible
  | isAssignable | isCopyAssignable | isMoveAssignable | isDestructible
  | isTriviallyCopyable | isStandardLayout | isEmpty
  | isTriviallyDefaultConstructible | isTriviallyCopyConstructible | isTriviallyMoveConstructible
  | isTriviallyAssignable | isTriviallyCopyAssignable | isTriviallyMoveAssignable
  | isTriviallyDestructible
  | isInvocable
  deriving Repr, DecidableEq, Inhabited

attribute [std rule "meta.unary.cat#3"] Trait.isVoid Trait.isIntegral Trait.isPointer
  Trait.isLvalueReference Trait.isRvalueReference Trait.isClass Trait.isFunction
attribute [std rule "meta.unary.comp#2"] Trait.isReference Trait.isObject Trait.isScalar
  Trait.isCompound Trait.isFundamental
attribute [std rule "meta.unary.prop#5"] Trait.isConst Trait.isDefaultConstructible
  Trait.isCopyConstructible Trait.isMoveConstructible Trait.isAssignable Trait.isCopyAssignable
  Trait.isMoveAssignable Trait.isDestructible Trait.isTriviallyCopyable Trait.isStandardLayout
  Trait.isEmpty Trait.isTriviallyDefaultConstructible Trait.isTriviallyCopyConstructible
  Trait.isTriviallyMoveConstructible Trait.isTriviallyAssignable Trait.isTriviallyCopyAssignable
  Trait.isTriviallyMoveAssignable Trait.isTriviallyDestructible
attribute [std rule "meta.unary.prop#9"] Trait.isConstructible
attribute [std rule "meta.rel#3"] Trait.isSame Trait.isBaseOf Trait.isInvocable
attribute [std rule "meta.rel#6"] Trait.isConvertible

namespace Trait

/-- The `std::` variable template that spells the trait. -/
def spelling : Trait → String
  | .isVoid => "std::is_void_v"
  | .isIntegral => "std::is_integral_v"
  | .isPointer => "std::is_pointer_v"
  | .isLvalueReference => "std::is_lvalue_reference_v"
  | .isRvalueReference => "std::is_rvalue_reference_v"
  | .isClass => "std::is_class_v"
  | .isFunction => "std::is_function_v"
  | .isReference => "std::is_reference_v"
  | .isObject => "std::is_object_v"
  | .isScalar => "std::is_scalar_v"
  | .isCompound => "std::is_compound_v"
  | .isFundamental => "std::is_fundamental_v"
  | .isConst => "std::is_const_v"
  | .isSame => "std::is_same_v"
  | .isBaseOf => "std::is_base_of_v"
  | .isConvertible => "std::is_convertible_v"
  | .isConstructible => "std::is_constructible_v"
  | .isDefaultConstructible => "std::is_default_constructible_v"
  | .isCopyConstructible => "std::is_copy_constructible_v"
  | .isMoveConstructible => "std::is_move_constructible_v"
  | .isAssignable => "std::is_assignable_v"
  | .isCopyAssignable => "std::is_copy_assignable_v"
  | .isMoveAssignable => "std::is_move_assignable_v"
  | .isDestructible => "std::is_destructible_v"
  | .isTriviallyCopyable => "std::is_trivially_copyable_v"
  | .isStandardLayout => "std::is_standard_layout_v"
  | .isEmpty => "std::is_empty_v"
  | .isTriviallyDefaultConstructible => "std::is_trivially_default_constructible_v"
  | .isTriviallyCopyConstructible => "std::is_trivially_copy_constructible_v"
  | .isTriviallyMoveConstructible => "std::is_trivially_move_constructible_v"
  | .isTriviallyAssignable => "std::is_trivially_assignable_v"
  | .isTriviallyCopyAssignable => "std::is_trivially_copy_assignable_v"
  | .isTriviallyMoveAssignable => "std::is_trivially_move_assignable_v"
  | .isTriviallyDestructible => "std::is_trivially_destructible_v"
  | .isInvocable => "std::is_invocable_v"

/-- Is the trait answered from the types alone, with no program? -/
def structural : Trait → Bool
  | .isVoid | .isIntegral | .isPointer | .isLvalueReference | .isRvalueReference | .isClass
  | .isFunction | .isReference | .isObject | .isScalar | .isCompound | .isFundamental | .isConst
  | .isSame => true
  | _ => false

/-- How many types the trait takes; `is_constructible` and `is_invocable`
take at least one. -/
def arity : Trait → Nat
  | .isSame | .isBaseOf | .isConvertible | .isAssignable | .isTriviallyAssignable => 2
  | _ => 1

/-- The unary traits, on one type. -/
def unary : Trait → Ty → Bool
  | .isVoid, t => t.isVoid
  | .isIntegral, t => t.isIntegral
  | .isPointer, t => t.isPointer
  | .isLvalueReference, t => t.isLvalueReference
  | .isRvalueReference, t => t.isRvalueReference
  | .isClass, t => t.isClass
  | .isFunction, t => t.isFunction
  | .isReference, t => t.isReference
  | .isObject, t => t.isObject
  | .isScalar, t => t.isScalar
  | .isCompound, t => t.isCompound
  | .isFundamental, t => t.isFundamental
  | .isConst, t => t.isConst
  | _, _ => false

/-- The trait's answer on its arguments, once substituted. A trait asked
of a type that is not concrete, or with the wrong number of arguments,
is an invalid expression in the immediate context: `soft`. -/
def answer (q : Trait) (ts : List Ty) : Subst Bool :=
  if !q.structural then .soft s!"{q.spelling} needs the program"
  else
    match q, ts with
    | .isSame, [a, b] =>
      if a.concrete && b.concrete then .ok (a == b) else .soft "is_same of a dependent type"
    | .isSame, _ => .soft "is_same takes two types"
    | q, [t] => if t.concrete then .ok (q.unary t) else .soft s!"{q.spelling} of a dependent type"
    | q, _ => .soft s!"{q.spelling} takes one type"

/-- A trait's answer is never a hard error: it is formed in the
immediate context, from the types alone. -/
theorem answer_not_hard (q : Trait) (ts : List Ty) (r : Reason) : q.answer ts ≠ .hard r := by
  unfold answer
  split
  · simp
  · split <;> (repeat' split) <;> simp

end Trait

end Overload
