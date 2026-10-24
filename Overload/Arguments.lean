-- Overload/Arguments.lean                                            -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Program
import Overload.Types

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

/-! ## Integer types

The integer types and their ranges are `Overload/Types.lean`'s
(`integerTypes`, `representable`). -/

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

/-! ## The conversion of an argument to its parameter -/

/-- The declared type of a constant template parameter as it stands with
the bindings so far, top-level cv-qualifiers ignored. -/
@[std rule "temp.param#11"]
def declaredType (σ : Bindings) (t : Ty) : Ty := (t.subst σ).stripConst

/-- Is the argument a value, a prvalue in the invented declaration? -/
def Ty.isValue : Ty → Bool
  | .value _ => true
  | _ => false

/-- Would the invented declaration `T x = E;` bind a reference to a
temporary: `T` a reference type, placeholder or not, and `E` a value?
A constant template parameter of reference type shall not refer to a
temporary, so this is a failure however the reference's type is
deduced. -/
@[std rule "temp.arg.nontype#6"]
def bindsTemporary (t a : Ty) : Bool := t.isRef && a.isValue

/-- A template argument converts to the value its parameter takes. For a
type parameter the argument is a type. For a constant parameter the
declared type decides: a placeholder takes the argument's own type,
whatever its spelling; otherwise the argument is a value, and a
dependent type is formed later, an integer type takes a converted
constant, a class type takes a value of that class or the base
subobject of a value of a derived class, through the oracle `sub`, and
a reference binds an object. -/
@[specification]
inductive ConvertsTo (sub : Ty → Val → Option Val) (σ : Bindings) :
    ParamKind → Ty → Ty → Prop where
  /-- A type for a type template parameter. -/
  | type (a : Ty) (h : a.isType = true) : ConvertsTo sub σ .type a a
  /-- The parameter's type contains a placeholder: it is deduced from
  the argument, which converts to itself, unless the type is a reference
  and the argument a value, which would bind a temporary. -/
  | placeholder (t a : Ty) (hp : (declaredType σ t).hasPlaceholder = true)
      (hv : bindsTemporary (declaredType σ t) a = false) :
      ConvertsTo sub σ (.const t) a a
  /-- The parameter's type still depends on a template parameter: it is
  formed when the parameter list is substituted, and the argument
  stands. -/
  | dependent (t a : Ty) (hp : (declaredType σ t).hasPlaceholder = false) (ha : a.isType = false)
      (hd : (declaredType σ t).dependent = true) : ConvertsTo sub σ (.const t) a a
  /-- An integer type: the argument is a converted constant expression
  of that type. -/
  | integer (t : Ty) (n : String) (v w : Val)
      (hp : (declaredType σ t).hasPlaceholder = false)
      (hd : (declaredType σ t).dependent = false)
      (ht : declaredType σ t = .named n) (hn : isInteger n = true)
      (hc : convertedConstant n v = .ok w) : ConvertsTo sub σ (.const t) (.value v) (.value w)
  /-- A class type and a value of that class: the temporary is the
  value. -/
  | classSame (t : Ty) (c : String) (vs : Val)
      (hp : (declaredType σ t).hasPlaceholder = false)
      (hd : (declaredType σ t).dependent = false)
      (ht : declaredType σ t = .named c) (hn : isInteger c = false) :
      ConvertsTo sub σ (.const t) (.value (.obj c vs)) (.value (.obj c vs))
  /-- A class type and a value of a class derived from it: the temporary
  is the base subobject. -/
  | classBase (t : Ty) (c d : String) (vs w : Val)
      (hp : (declaredType σ t).hasPlaceholder = false)
      (hd : (declaredType σ t).dependent = false)
      (ht : declaredType σ t = .named c) (hn : isInteger c = false) (hne : c ≠ d)
      (hs : sub (.named c) (.obj d vs) = some w) :
      ConvertsTo sub σ (.const t) (.value (.obj d vs)) (.value w)
  /-- An lvalue reference and an object: the reference binds directly. -/
  | reference (t r u : Ty)
      (hp : (declaredType σ t).hasPlaceholder = false)
      (hd : (declaredType σ t).dependent = false)
      (ht : declaredType σ t = .lref u) : ConvertsTo sub σ (.const t) (.ref r) (.ref r)

attribute [std rule "temp.arg.general#1.sentence-1"] ConvertsTo.type
attribute [std rule "temp.arg.nontype#1.sentence-2"] ConvertsTo.placeholder
attribute [std rule "temp.deduct.general#5.sentence-4"] ConvertsTo.dependent
attribute [std rule "temp.arg.nontype#2.sentence-2"] ConvertsTo.integer
attribute [std rule "temp.arg.nontype#5"] ConvertsTo.classSame
attribute [std rule "temp.arg.nontype#3.sentence-1"] ConvertsTo.classBase
attribute [std rule "expr.const.const#8"] ConvertsTo.reference

/-- The class cases of the conversion: a value of the parameter's class,
or the base subobject of a value of a derived class. -/
def convertClass (sub : Ty → Val → Option Val) (c : String) : Val → Subst Ty
  | .obj d vs =>
    if c = d then .ok (.value (.obj d vs))
    else match sub (.named c) (.obj d vs) with
      | some w => .ok (.value w)
      | none => .soft s!"{d} has no one base class subobject of type {c}"
  | v => .soft s!"{repr v} is not a value of class type {c}"

/-- The conversion, as a function. It never fails hard: every failure
is a deduction failure (`convertArg_not_hard`). A value for a reference
parameter would bind a temporary, which a constant template parameter of
reference type shall not refer to. -/
@[std rule "temp.arg.nontype#6"]
def convertArg (sub : Ty → Val → Option Val) (σ : Bindings) : ParamKind → Ty → Subst Ty
  | .type, a => if a.isType then .ok a else .soft "a value for a type template parameter"
  | .const t, a =>
    let t' := declaredType σ t
    if t'.hasPlaceholder then
      if bindsTemporary t' a then .soft "a reference parameter binds an object, not a temporary"
      else .ok a
    else if a.isType then .soft "a type for a constant template parameter"
    else if t'.dependent then .ok a
    else
      match t', a with
      | .named n, .value v =>
        if isInteger n then (convertedConstant n v).map .value else convertClass sub n v
      | .lref _, .ref r => .ok (.ref r)
      | .lref _, _ => .soft "a reference parameter binds an object, not a temporary"
      | _, _ => .soft "no conversion of the argument to the parameter's type"

/-- Agreement of the relation and the function. -/
theorem convertArg_iff (sub : Ty → Val → Option Val) (σ : Bindings) (k : ParamKind) (a a' : Ty) :
    ConvertsTo sub σ k a a' ↔ convertArg sub σ k a = .ok a' := by
  constructor
  · intro h
    cases h with
    | type a h => simp [convertArg, h]
    | placeholder t a hp hv => simp [convertArg, hp, hv]
    | dependent t a hp ha hd => simp [convertArg, ha, hp, hd]
    | integer t n v w hp hd ht hn hc =>
      rw [ht] at hp hd
      simp [convertArg, hp, hd, ht, hn, hc, Ty.isType, Subst.map]
    | classSame t c vs hp hd ht hn =>
      rw [ht] at hp hd
      simp [convertArg, convertClass, hp, hd, ht, hn, Ty.isType]
    | classBase t c d vs w hp hd ht hn hne hs =>
      rw [ht] at hp hd
      simp [convertArg, convertClass, hp, hd, ht, hn, hne, hs, Ty.isType]
    | reference t r u hp hd ht =>
      rw [ht] at hp hd
      simp [convertArg, hp, hd, ht, Ty.isType]
  · intro h
    cases k with
    | type =>
      by_cases ha : a.isType = true
      · simp [convertArg, ha] at h; subst h; exact .type a ha
      · simp [convertArg, ha] at h
    | const t =>
      by_cases hp : (declaredType σ t).hasPlaceholder = true
      · by_cases hv : bindsTemporary (declaredType σ t) a = true
        · simp [convertArg, hp, hv] at h
        · have hv' : bindsTemporary (declaredType σ t) a = false := by simpa using hv
          simp [convertArg, hp, hv'] at h; subst h; exact .placeholder t a hp hv'
      · have hp' : (declaredType σ t).hasPlaceholder = false := by simpa using hp
        by_cases ha : a.isType = true
        · simp [convertArg, hp', ha] at h
        · have ha' : a.isType = false := by simpa using ha
          by_cases hd : (declaredType σ t).dependent = true
          · simp [convertArg, hp', ha', hd] at h; subst h; exact .dependent t a hp' ha' hd
          · have hd' : (declaredType σ t).dependent = false := by simpa using hd
            simp only [convertArg, hp', ha', hd', Bool.false_eq_true, ↓reduceIte] at h
            generalize ht : declaredType σ t = t' at h
            cases t' <;> cases a <;> try simp at h
            case named.value n v =>
              by_cases hn : isInteger n = true
              · simp only [hn, ↓reduceIte] at h
                cases hc : convertedConstant n v <;> simp [hc, Subst.map] at h
                subst h
                exact .integer t n v _ hp' hd' ht hn hc
              · have hn' : isInteger n = false := by simpa using hn
                simp only [hn', Bool.false_eq_true, ↓reduceIte] at h
                cases v with
                | obj d vs =>
                  by_cases hcd : n = d
                  · simp [convertClass, hcd] at h
                    subst h; subst hcd
                    exact .classSame t n vs hp' hd' ht hn'
                  · simp only [convertClass, hcd, ↓reduceIte] at h
                    cases hs : sub (.named n) (.obj d vs) <;> simp [hs] at h
                    subst h
                    exact .classBase t n d vs _ hp' hd' ht hn' hcd hs
                | _ => simp [convertClass] at h
            case lref.ref u r =>
              try simp at h
              subst h
              exact .reference t r u hp' hd' ht

/-- The conversion never fails outside the immediate context. -/
theorem convertArg_not_hard (sub : Ty → Val → Option Val) (σ : Bindings) (k : ParamKind) (a : Ty)
    (r : Reason) : convertArg sub σ k a ≠ .hard r := by
  cases k with
  | type => by_cases ha : a.isType = true <;> simp [convertArg, ha]
  | const t =>
    by_cases hp : (declaredType σ t).hasPlaceholder = true
    · by_cases hv : bindsTemporary (declaredType σ t) a = true <;> simp [convertArg, hp, hv]
    · have hp' : (declaredType σ t).hasPlaceholder = false := by simpa using hp
      by_cases ha : a.isType = true
      · simp [convertArg, hp', ha]
      · have ha' : a.isType = false := by simpa using ha
        by_cases hd : (declaredType σ t).dependent = true
        · simp [convertArg, hp', ha', hd]
        · have hd' : (declaredType σ t).dependent = false := by simpa using hd
          simp only [convertArg, hp', ha', hd', Bool.false_eq_true, ↓reduceIte]
          generalize declaredType σ t = t'
          cases t' <;> cases a
          all_goals try (simp; done)
          case named.value n v =>
            by_cases hn : isInteger n = true
            · simp only [hn, ↓reduceIte]
              cases hc : convertedConstant n v with
              | hard r' => exact absurd hc (convertedConstant_not_hard n v r')
              | ok w => simp [Subst.map]
              | soft r' => simp [Subst.map]
            · have hn' : isInteger n = false := by simpa using hn
              simp only [hn', Bool.false_eq_true, ↓reduceIte]
              cases v with
              | obj d vs =>
                by_cases hcd : n = d
                · simp [convertClass, hcd]
                · simp only [convertClass, hcd, ↓reduceIte]
                  cases sub (.named n) (.obj d vs) <;> simp
              | _ => simp [convertClass]

/-! ### The identities the typeclass side uses -/

/-- A type argument converts to itself. -/
@[simp]
theorem convertArg_type (sub : Ty → Val → Option Val) (σ : Bindings) (a : Ty) (h : a.isType = true) :
    convertArg sub σ .type a = .ok a := by
  simp [convertArg, h]

/-- An argument for a parameter whose type contains a placeholder
converts to itself, unless a reference would bind a temporary. -/
@[simp]
theorem convertArg_placeholder (sub : Ty → Val → Option Val) (σ : Bindings) (t a : Ty)
    (hp : (declaredType σ t).hasPlaceholder = true)
    (hv : bindsTemporary (declaredType σ t) a = false) :
    convertArg sub σ (.const t) a = .ok a := by
  simp [convertArg, hp, hv]

/-- `auto`. -/
@[simp]
theorem convertArg_auto (sub : Ty → Val → Option Val) (σ : Bindings) (a : Ty) :
    convertArg sub σ (.const (.named "auto")) a = .ok a :=
  convertArg_placeholder sub σ _ a rfl rfl

/-- `const auto&`, for an argument that is not a value. -/
@[simp]
theorem convertArg_auto_ref (sub : Ty → Val → Option Val) (σ : Bindings) (a : Ty)
    (hv : a.isValue = false) :
    convertArg sub σ (.const (.lref (.const (.named "auto")))) a = .ok a :=
  convertArg_placeholder sub σ _ a rfl (by simp [bindsTemporary, declaredType, Ty.isRef, hv])

/-- `const auto&` and a value: the reference would bind a temporary, and
the conversion is a deduction failure. A prvalue, such as the result of
a user-defined conversion, has no object for a reference parameter to
denote. -/
@[std theorem "temp.arg.nontype#6"]
theorem placeholder_reference_refuses_value (sub : Ty → Val → Option Val) (σ : Bindings) (v : Val) :
    ∃ r, convertArg sub σ (.const (.lref (.const (.named "auto")))) (.value v) = .soft r :=
  have hd : declaredType σ (.lref (.const (.named "auto"))) = .lref (.const (.named "auto")) := rfl
  ⟨"a reference parameter binds an object, not a temporary",
    by simp [convertArg, hd, bindsTemporary, Ty.isRef, Ty.isValue, Ty.hasPlaceholder]⟩

/-- The oracle is consulted only for a class value of another class
than the parameter's: two oracles that agree on the argument's value
give one conversion. -/
theorem convertArg_congr (sub₁ sub₂ : Ty → Val → Option Val) (σ : Bindings) (k : ParamKind) (a : Ty)
    (h : ∀ d vs, a = .value (.obj d vs) → ∀ c, sub₁ (.named c) (.obj d vs) = sub₂ (.named c) (.obj d vs)) :
    convertArg sub₁ σ k a = convertArg sub₂ σ k a := by
  cases k with
  | type => rfl
  | const t =>
    by_cases hp : (declaredType σ t).hasPlaceholder = true
    · simp [convertArg, hp]
    · have hp' : (declaredType σ t).hasPlaceholder = false := by simpa using hp
      by_cases ha : a.isType = true
      · simp [convertArg, hp', ha]
      · have ha' : a.isType = false := by simpa using ha
        by_cases hd : (declaredType σ t).dependent = true
        · simp [convertArg, hp', ha', hd]
        · have hd' : (declaredType σ t).dependent = false := by simpa using hd
          simp only [convertArg, hp', ha', hd', Bool.false_eq_true, ↓reduceIte]
          generalize declaredType σ t = t'
          cases t' <;> cases a
          all_goals try rfl
          case named.value n v =>
            by_cases hn : isInteger n = true
            · simp [hn]
            · have hn' : isInteger n = false := by simpa using hn
              simp only [hn', Bool.false_eq_true, ↓reduceIte]
              cases v with
              | obj d vs => simp only [convertClass]; rw [h d vs rfl n]
              | _ => rfl

/-- The template parameter object is template-argument-equivalent to the
temporary, and the fragment's equivalence is equality: its value is the
temporary's, which is what the binding records. -/
@[std theorem "temp.arg.nontype#4"]
theorem tpo_value (v : Val) : ∀ P : Val, Val.Equivalent P v → P = v :=
  fun _ h => h.eq

end Overload
