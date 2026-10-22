-- Overload/Arguments.lean                                            -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Program

/-!
# Template arguments and their conversion

A constant template argument is converted to its parameter's declared
type ([temp.arg.nontype]). For a type that is not a class the argument
is a converted constant expression of that type ([temp.arg.nontype]/2),
whose implicit conversion may contain integral promotions and integral
conversions other than narrowing ([expr.const.const]/8); an integral
conversion narrows when the target type cannot represent every value of
the source type and the value, a constant, does not fit it
([dcl.init.list]/7). This module has the integer types of the fragment
and their ranges, the type of an integer literal, narrowing as relation
and function, and the converted constant. The class case and the
conversion of an argument against a parameter of any kind follow it
(`convertArg`).

The theorem: for a constant source, narrowing is exactly the value not
being representable in the target (`narrowing_constant`). The two halves
of the Standard's rule, the ranges and the value, collapse into one
because a constant's value lies in its own type's range.
-/

namespace Overload

/-! ## Integer types -/

/-- The integer types of the fragment, by name, with the least and
greatest value each represents. The widths are the `integer-widths`
decision: LP64, `char` signed, and `bool` an integer type with range 0
to 1. -/
@[assumed "integer-widths"]
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

/-- Does the target type represent every value of the source type: its
range includes the source's. -/
def covers (tgt src : String) : Option Bool :=
  match integerRange tgt, integerRange src with
  | some (lo, hi), some (lo', hi') => some (decide (lo ≤ lo' ∧ hi' ≤ hi))
  | _, _ => none

/-- The type of an integer literal: the first of `int`, `long` and
`long long` in which its value can be represented. A negative argument
is unary minus applied to a literal, so the magnitude decides; the
value `-2^63` has no type, since `2^63` has none. -/
@[std rule "lex.icon#3.sentence-1"]
def literalType (n : Int) : Option String :=
  ["int", "long", "long long"].find? fun t => (representable t n.natAbs).getD false

/-- The type of a constant argument's source expression: an integer
literal's, `bool`, or a class value's class. A value carries no type of
its own (`decisions.md#value-typing`). -/
def Val.sourceType : Val → Option Ty
  | .int n => (literalType n).map .named
  | .bool _ => some (.named "bool")
  | .obj c _ => some (.named c)
  | _ => none

/-- Does a type contain a placeholder type: `auto` or a constrained
`C auto`, under any of `const`, pointer or reference? -/
@[std rule "temp.param#11"]
def Ty.hasPlaceholder : Ty → Bool
  | .named "auto" | .spec "auto" _ => true
  | .const t | .ptr t | .lref t | .rref t => Ty.hasPlaceholder t
  | _ => false

/-! ## Narrowing -/

/-- An integral conversion is narrowing: from an integer type to an
integer type that cannot represent all the values of the original type,
except where the source is a constant expression whose value after
integral promotions will fit into the target type. Every source in the
fragment is a constant, and promotion keeps a value, so the exception is
that the value is representable in the target. -/
@[specification]
inductive Narrowing (src tgt : String) (v : Int) : Prop where
  /-- Both are integer types, the target does not cover the source's
  range, and the value does not fit the target. -/
  | integer (hcovers : covers tgt src = some false)
      (hfit : representable tgt v = some false) : Narrowing src tgt v

attribute [std rule "dcl.init.list#7"] Narrowing.integer

/-- The function: narrowing when the target does not cover the source's
range and the value does not fit; `none` when either name is not an
integer type. -/
def narrowing (src tgt : String) (v : Int) : Option Bool :=
  match covers tgt src, representable tgt v with
  | some c, some f => some (!c && !f)
  | _, _ => none

theorem narrowing_iff (src tgt : String) (v : Int) :
    Narrowing src tgt v ↔ narrowing src tgt v = some true := by
  constructor
  · rintro ⟨hc, hf⟩
    simp [narrowing, hc, hf]
  · intro h
    unfold narrowing at h
    cases hc : covers tgt src with
    | none => simp [hc] at h
    | some c =>
      cases hf : representable tgt v with
      | none => simp [hc, hf] at h
      | some f =>
        simp [hc, hf] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hc, hf⟩

/-- For a constant source the value lies in its own type's range, so
when the target covers the source the value fits, and narrowing is
exactly the value not being representable in the target. -/
theorem narrowing_constant (src tgt : String) (v : Int)
    (hv : representable src v = some true) (ht : isInteger tgt = true) :
    narrowing src tgt v = some (!(representable tgt v).getD true) := by
  unfold narrowing covers representable isInteger at *
  cases hs : integerRange src with
  | none => simp [hs] at hv
  | some r =>
    obtain ⟨lo', hi'⟩ := r
    cases hgt : integerRange tgt with
    | none => simp [hgt] at ht
    | some q =>
      obtain ⟨lo, hi⟩ := q
      simp [hs] at hv
      by_cases hf : lo ≤ v ∧ v ≤ hi
      · simp [hf]
      · simp [hf, show ¬(lo ≤ lo' ∧ hi' ≤ hi) by omega]

/-! ## The converted constant -/

/-- An integral conversion admitted in a converted constant expression:
an integral promotion, or an integral conversion other than a narrowing
one. On the fragment's values both keep the value, so the conversion is
the value itself when it does not narrow. -/
@[std rule "expr.const.const#8"]
def integralConversion (src tgt : String) (v : Int) : Subst Int :=
  match narrowing src tgt v with
  | some false => .ok v
  | some true => .soft s!"narrowing conversion of {v} from {src} to {tgt}"
  | none => .soft s!"no conversion from {src} to {tgt}"

/-- The value of a constant template parameter of non-class type `t`
from a value argument: the argument shall be a converted constant
expression of type `t`, and the value of the parameter is the argument
as converted. A `bool` target takes the converted value as a `bool`; a
`bool` source converts as 0 or 1. -/
@[std rule "temp.arg.nontype#2.sentence-2"]
def convertedConstant (t : String) : Val → Subst Val
  | .int n =>
    match literalType n with
    | some src =>
      (integralConversion src t n).map fun w => if t = "bool" then .bool (w != 0) else .int w
    | none => .soft s!"{n} is not representable in any integer type"
  | .bool b =>
    (integralConversion "bool" t (if b then 1 else 0)).map fun w =>
      if t = "bool" then .bool b else .int w
  | v => .soft s!"{repr v} is not a converted constant expression of type {t}"

theorem integralConversion_not_hard (src tgt : String) (v : Int) (r : Reason) :
    integralConversion src tgt v ≠ .hard r := by
  unfold integralConversion
  cases narrowing src tgt v with
  | none => simp
  | some b => cases b <;> simp

/-- The conversion of a constant never fails outside the immediate
context: its failures are deduction failures. -/
theorem convertedConstant_not_hard (t : String) (v : Val) (r : Reason) :
    convertedConstant t v ≠ .hard r := by
  cases v with
  | int n =>
    unfold convertedConstant
    cases h : literalType n with
    | none => simp [h]
    | some src =>
      simp only [h]
      cases h' : integralConversion src t n with
      | hard r' => exact absurd h' (integralConversion_not_hard src t n r')
      | ok w => simp [Subst.map]
      | soft r' => simp [Subst.map]
  | bool b =>
    unfold convertedConstant
    cases h' : integralConversion "bool" t (if b then 1 else 0) with
    | hard r' => exact absurd h' (integralConversion_not_hard _ _ _ r')
    | ok w => simp [Subst.map, h']
    | soft r' => simp [Subst.map, h']
  | _ => simp [convertedConstant]

end Overload
