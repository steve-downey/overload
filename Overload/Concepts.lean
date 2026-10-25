-- Overload/Concepts.lean                                             -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Models

/-!
# The library's concepts, with their semantic requirements

The concepts of [concepts.lang], [concepts.compare], [concepts.object]
and [concepts.callable] as the fragment can state them: a `Program` of
concept definitions over the traits of phase 12, with a residue atom for
each expression the fragment lacks, and a `semantic` declaration for each
requirement the concept's specification gives beyond its body. The
expressions declared in a library requires-expression are required to be
equality-preserving unless the text says otherwise ([concepts.equality]/4),
so a concept with such an expression carries that law too; `invocable`
says otherwise, and `regular_invocable` says it after all.

Two departures from the text. A concept-id takes a fixed number of
arguments, so `constructible_from` and `invocable` are stated for one
argument type after the first and the one-argument use of
`constructible_from` is written out; and `T{}` and `T t;` are both
`is_default_constructible` here, since the fragment's value-initialization
of a class is its default-initialization.
-/

namespace Overload

namespace Concepts

/-- The parameters of a concept body. -/
private def T : Ty := .param 0
private def U : Ty := .param 1
private def tparam : TemplateParam := { kind := .type }

/-! ## The semantic requirements -/

/-- The implicit and explicit conversions produce equal results, and the
source is left as the text says. -/
@[std rule "concept.convertible#2"]
def convertibleToEqual : Semantic :=
  { slug := "convertible-to-equal"
    statement := "static_cast<To>(f()) is equal to the implicit conversion test(f); an rvalue source is left valid but unspecified, any other source unmodified" }

/-- A move leaves the new object equal to the old value and the source
valid but unspecified. -/
@[std rule "concept.moveconstructible#1"]
def moveConstructibleEqual : Semantic :=
  { slug := "move-constructible-equal"
    statement := "after T u = rv; and in T(rv), the result is equal to the value rv had; a non-const rv is left valid but unspecified, a const one unchanged" }

/-- A copy equals the original and does not modify it. -/
@[std rule "concept.copyconstructible#1"]
def copyConstructibleEqual : Semantic :=
  { slug := "copy-constructible-equal"
    statement := "after T u = v; and in T(v), the result is equal to v and v is not modified" }

/-- Assignment returns the object assigned to and leaves it equal to the
value assigned. -/
@[std rule "concept.assignable#1" "concept.assignable#2"]
def assignableFromEqual : Semantic :=
  { slug := "assignable-from-equal"
    statement := "addressof(lhs = rhs) == addressof(lcopy); afterwards lhs is equal to the value rhs had, a non-const xvalue rhs is left valid but unspecified and any other glvalue rhs unmodified; assignment need not be total" }

/-- A swap exchanges the values denoted. -/
@[std rule "concept.swappable#1" "concept.swappable#2" "concept.swappable#3" "concept.swappable#4"]
def swapExchanges : Semantic :=
  { slug := "swap-exchanges-values"
    statement := "ranges::swap(E1, E2) exchanges the values denoted by E1 and E2 and modifies neither of two distinct equal objects; a selected swap that does not is ill-formed, no diagnostic required" }

/-- A boolean-testable type declares no logical operators of its own. -/
@[std rule "concept.booleantestable#2"]
def booleanTestableNoLogicalOperators : Semantic :=
  { slug := "boolean-testable-no-logical-operators"
    statement := "either the type is not a class or a search for operator&& and operator|| in its scope finds nothing, and argument-dependent lookup for them with the type as the only argument finds no disqualifying declaration" }

/-- The four comparisons share a domain and agree. -/
@[std rule "concept.equalitycomparable#1"]
def weaklyEqualityComparable : Semantic :=
  { slug := "weakly-equality-comparable"
    statement := "t == u, u == t, t != u and u != t have the same domain; bool(u == t) == bool(t == u); bool(t != u) == !bool(t == u); bool(u != t) == bool(t != u)" }

/-- `==` is `true` exactly for equal values. -/
@[std rule "concept.equalitycomparable#2" "concept.equalitycomparable#3"]
def equalityComparableEqual : Semantic :=
  { slug := "equality-comparable-equal"
    statement := "bool(a == b) is true when a is equal to b and false otherwise; with equality preservation this makes == symmetric and transitive" }

/-- The call is equality-preserving and modifies neither the function
object nor the arguments. -/
@[std rule "concept.regularinvocable#1" "concept.regularinvocable#2" "concept.regularinvocable#3"]
def regularInvocableEqualityPreserving : Semantic :=
  { slug := "regular-invocable-equality-preserving"
    statement := "the invoke expression is equality-preserving and does not modify the function object or the arguments; a random number generator does not model it, and the distinction from invocable is purely semantic" }

/-- The laws every library requires-expression carries unless its text
says otherwise. -/
@[std rule "concepts.equality#4"]
def expressionLaws (c : String) : List Decl :=
  libraryExpressionsPreserveEquality.map (.semantic c ·)

/-! ## The concepts -/

/-- `same_as<T, U> = is_same_v<T, U> && is_same_v<U, T>`. -/
@[std rule "concept.same#1"]
def sameAs : List Decl :=
  [.conceptDef "same_as" 2 (.conj (.trait .isSame [T, U]) (.trait .isSame [U, T]))]

/-- `derived_from<Derived, Base> = is_base_of_v<Base, Derived> &&
is_convertible_v<const volatile Derived*, const volatile Base*>`, the
pointer conversion a residue atom. -/
@[std rule "concept.derived#1"]
def derivedFrom : List Decl :=
  [ .concept "pointer_convertible" "std::is_convertible_v<const volatile T0*, const volatile T1*>" 2
  , .conceptDef "derived_from" 2 (.conj (.trait .isBaseOf [U, T]) (.atomic "pointer_convertible" [T, U])) ]

/-- `convertible_to<From, To> = is_convertible_v<From, To> && requires {
static_cast<To>(declval<From>()); }`, the cast a residue atom. -/
@[std rule "concept.convertible#1"]
def convertibleTo : List Decl :=
  [ .concept "static_castable" "requires { static_cast<T1>(std::declval<T0>()); }" 2
  , .conceptDef "convertible_to" 2 (.conj (.trait .isConvertible [T, U]) (.atomic "static_castable" [T, U]))
  , .semantic "convertible_to" convertibleToEqual ] ++ expressionLaws "convertible_to"

/-- `destructible<T> = is_nothrow_destructible_v<T>`: the concept forbids
a potentially-throwing destructor, which `is_nothrow_destructible`
decides through the implicit exception specifications. -/
@[std rule "concept.destructible#1"]
def destructible : List Decl :=
  [.conceptDef "destructible" 1 (.trait .isNothrowDestructible [T])]

/-- `constructible_from<T, Arg> = destructible<T> && is_constructible_v<T, Arg>`,
for one argument type. -/
@[std rule "concept.constructible#1"]
def constructibleFrom : List Decl :=
  [.conceptDef "constructible_from" 2 (.conj (.conceptId "destructible" [T]) (.trait .isConstructible [T, U]))]

/-- `default_initializable<T> = constructible_from<T> && requires { T{}; } &&
is-default-initializable<T>`: destructible, and `T t;` well-formed. -/
@[std rule "concept.default.init#1"]
def defaultInitializable : List Decl :=
  [.conceptDef "default_initializable" 1
    (.conj (.conceptId "destructible" [T]) (.trait .isDefaultConstructible [T]))]

/-- `move_constructible<T> = constructible_from<T, T> && convertible_to<T, T>`. -/
@[std rule "concept.moveconstructible#1"]
def moveConstructible : List Decl :=
  [ .conceptDef "move_constructible" 1
      (.conj (.conceptId "constructible_from" [T, T]) (.conceptId "convertible_to" [T, T]))
  , .semantic "move_constructible" moveConstructibleEqual ]

/-- `copy_constructible<T>`: move constructible, and constructible from and
convertible from `T&`, `const T&` and `const T`. -/
@[std rule "concept.copyconstructible#1"]
def copyConstructible : List Decl :=
  [ .conceptDef "copy_constructible" 1
      (.conj (.conceptId "move_constructible" [T])
        (.conj (.conj (.conceptId "constructible_from" [T, .lref T]) (.conceptId "convertible_to" [.lref T, T]))
          (.conj (.conj (.conceptId "constructible_from" [T, .lref (.const T)])
                        (.conceptId "convertible_to" [.lref (.const T), T]))
                 (.conj (.conceptId "constructible_from" [T, .const T]) (.conceptId "convertible_to" [.const T, T])))))
  , .semantic "copy_constructible" copyConstructibleEqual ]

/-- `assignable_from<LHS, RHS>`: an lvalue reference, a common reference
(a residue atom), and `lhs = forward<RHS>(rhs)` of type `LHS`. -/
@[std rule "concept.assignable#1"]
def assignableFrom : List Decl :=
  [ .concept "common_reference_with" "true" 2
  , .conceptDef "assignable_from" 2
      (.conj (.trait .isLvalueReference [T])
        (.conj (.atomic "common_reference_with" [T, U]) (.trait .isAssignable [T, U])))
  , .semantic "assignable_from" assignableFromEqual ] ++ expressionLaws "assignable_from"

/-- `swappable<T> = requires(T& a, T& b) { ranges::swap(a, b); }`, the
swap a residue atom. -/
@[std rule "concept.swappable#3"]
def swappable : List Decl :=
  [ .concept "swappable_lvalues" "requires(T& a, T& b) { std::swap(a, b); }"
  , .conceptDef "swappable" 1 (.atomic "swappable_lvalues" [T])
  , .semantic "swappable" swapExchanges ] ++ expressionLaws "swappable"

/-- `boolean-testable-impl<T> = convertible_to<T, bool>`. -/
@[std rule "concept.booleantestable#1"]
def booleanTestable : List Decl :=
  [ .conceptDef "boolean_testable" 1 (.conceptId "convertible_to" [T, .named "bool"])
  , .semantic "boolean_testable" booleanTestableNoLogicalOperators ]

/-- `equality_comparable<T> = weakly-equality-comparable-with<T, T>`: the
four comparisons boolean-testable, a residue atom. -/
@[std rule "concept.equalitycomparable#1"]
def equalityComparable : List Decl :=
  [ .concept "equality_operators"
      "requires(const T& a, const T& b) { static_cast<bool>(a == b); static_cast<bool>(a != b); }"
  , .conceptDef "equality_comparable" 1 (.atomic "equality_operators" [T])
  , .semantic "equality_comparable" weaklyEqualityComparable
  , .semantic "equality_comparable" equalityComparableEqual ] ++ expressionLaws "equality_comparable"

/-- `movable`, `copyable`, `semiregular`, `regular`. -/
@[std rule "concepts.object#1" "concepts.object#2" "concepts.object#3"]
def objectConcepts : List Decl :=
  [ .conceptDef "movable" 1
      (.conj (.trait .isObject [T])
        (.conj (.conceptId "move_constructible" [T])
          (.conj (.conceptId "assignable_from" [.lref T, T]) (.conceptId "swappable" [T]))))
  , .conceptDef "copyable" 1
      (.conj (.conceptId "copy_constructible" [T])
        (.conj (.conceptId "movable" [T])
          (.conj (.conceptId "assignable_from" [.lref T, .lref T])
            (.conj (.conceptId "assignable_from" [.lref T, .lref (.const T)])
                   (.conceptId "assignable_from" [.lref T, .const T])))))
  , .conceptDef "semiregular" 1 (.conj (.conceptId "copyable" [T]) (.conceptId "default_initializable" [T]))
  , .conceptDef "regular" 1 (.conj (.conceptId "semiregular" [T]) (.conceptId "equality_comparable" [T])) ]

/-- `invocable<F, Arg>` by `invoke`, not required to be equality-preserving;
`regular_invocable<F, Arg> = invocable<F, Arg>`, with the law. -/
@[std rule "concept.invocable#1" "concept.invocable#2" "concept.regularinvocable#1"]
def callableConcepts : List Decl :=
  [ .conceptDef "invocable" 2 (.trait .isInvocable [T, U])
  , .conceptDef "regular_invocable" 2 (.conceptId "invocable" [T, U])
  , .semantic "regular_invocable" regularInvocableEqualityPreserving ]

/-- The library's concepts as the fragment states them. -/
def libraryConcepts : Program :=
  sameAs ++ derivedFrom ++ convertibleTo ++ destructible ++ constructibleFrom ++ defaultInitializable ++
    moveConstructible ++ copyConstructible ++ assignableFrom ++ swappable ++ booleanTestable ++
    equalityComparable ++ objectConcepts ++ callableConcepts

end Concepts

open Concepts

/-- `same_as<T, U>` subsumes `same_as<U, T>` and vice versa: the two normal
forms have the same atoms. -/
@[std theorem "concept.same#1"]
theorem same_as_symmetric :
    Constraint.subsumes (libraryConcepts.normalize (.conceptId "same_as" [.param 0, .param 1]))
        (libraryConcepts.normalize (.conceptId "same_as" [.param 1, .param 0])) = true ∧
    Constraint.subsumes (libraryConcepts.normalize (.conceptId "same_as" [.param 1, .param 0]))
        (libraryConcepts.normalize (.conceptId "same_as" [.param 0, .param 1])) = true := by
  decide +kernel

/-- The object concepts refine one another by normalization: `regular`
subsumes `semiregular`, which subsumes `copyable`, which subsumes
`copy_constructible`, which subsumes `move_constructible`, and none the
other way. -/
@[std theorem "concepts.object#1"]
theorem regular_refines :
    let n (c : String) := libraryConcepts.normalize (.conceptId c [.param 0])
    Constraint.subsumes (n "regular") (n "semiregular") = true ∧
    Constraint.subsumes (n "semiregular") (n "copyable") = true ∧
    Constraint.subsumes (n "copyable") (n "copy_constructible") = true ∧
    Constraint.subsumes (n "copy_constructible") (n "move_constructible") = true ∧
    Constraint.subsumes (n "semiregular") (n "regular") = false ∧
    Constraint.subsumes (n "copyable") (n "semiregular") = false ∧
    Constraint.subsumes (n "move_constructible") (n "copy_constructible") = false := by
  decide +kernel

/-- `regular_invocable` and `invocable` have one normal form, so they are
satisfied together; they differ in the law the first owes. -/
@[std theorem "concept.regularinvocable#3"]
theorem regular_invocable_semantic_only :
    libraryConcepts.normalize (.conceptId "regular_invocable" [.param 0, .param 1]) =
      libraryConcepts.normalize (.conceptId "invocable" [.param 0, .param 1]) ∧
    libraryConcepts.laws "invocable" = [] ∧
    libraryConcepts.laws "regular_invocable" = [regularInvocableEqualityPreserving] := by
  decide +kernel

/-- Modelling `regular` is modelling every concept it is defined in terms
of: its laws are the ten of `equality_comparable`, `copy_constructible`,
`move_constructible`, `convertible_to`, `assignable_from` and `swappable`
and of the library's requires-expressions, each once. -/
@[std theorem "res.on.requirements#1"]
theorem regular_laws :
    (libraryConcepts.laws "regular").length = 10 ∧
    [ weaklyEqualityComparable, equalityComparableEqual, equalityPreserving, stable, nonModifying
    , copyConstructibleEqual, moveConstructibleEqual, convertibleToEqual, assignableFromEqual
    , swapExchanges ].all (libraryConcepts.laws "regular").contains = true := by
  decide +kernel

end Overload
