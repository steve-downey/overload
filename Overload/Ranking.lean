-- Overload/Ranking.lean                                              -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Resolution

/-!
# A concrete conversion ranking

The ranking that `ranking-fidelity` calls for: one concrete instance of
`Ranking`, covering what priority tags and reference binding need. The
core theorems keep the ranking a parameter; this one is what the emitted
call cases are computed with, so the model can say which dispatch styles
are safe.

The fragment has class types and no arithmetic, so the standard
conversion sequences it forms are the identity conversion, which is an
Exact Match, and the derived-to-base conversion, which has Conversion
rank ([over.best.ics.general]/7). A reference binds directly or not at
all: without user-defined conversions there is no temporary to bind to
([over.ics.ref]/2).

Comparison follows [over.ics.rank]/3 as a lexicographic chain, one tier
per "or, if not that":

1. the subsequence rule and rank, with the derived-to-base rules of /4
   that distinguish two Conversions;
2. an rvalue reference bound to an rvalue over an lvalue reference;
3. a reference to the less qualified of two reference-compatible types.

A tier that holds in both directions, which only a cyclic class hierarchy
can make happen, decides nothing, so `better` is asymmetric by
construction (`better_asymm`).
-/

namespace Overload

namespace Program

/-- The direct base classes a program declares for a class, from its
first definition. A class template specialization has none: the fragment
does not give class templates bases. -/
def directBases (p : Program) : Ty → List Ty
  | .named n =>
    (p.findSome? fun
      | .class m bs ps _ => if m = n then some (bs ++ ps) else none
      | _ => none).getD []
  | _ => []

/-- `derivesWithin p fuel d b`: `b` is a base class of `d`, found within
`fuel` steps of direct derivation. -/
def derivesWithin (p : Program) : Nat → Ty → Ty → Bool
  | 0, _, _ => false
  | fuel + 1, d, b => (p.directBases d).any fun m => m == b || p.derivesWithin fuel m b

/-- A class `B` is a base class of `D` if it is a direct base class of
`D` or a direct base class of one of `D`'s base classes. A base class is
complete before the class that names it, so a chain of derivation is no
longer than the program, which bounds the search. -/
@[std rule "class.derived.general#2"]
def derives (p : Program) (d b : Ty) : Bool := p.derivesWithin p.length d b

/-- The base classes of a class, direct and indirect, within `fuel` steps
of direct derivation, nearest first. -/
def allBasesWithin (p : Program) : Nat → Ty → List Ty
  | 0, _ => []
  | fuel + 1, d => (p.directBases d).flatMap fun m => m :: p.allBasesWithin fuel m

/-- The base classes of a class, direct and indirect. -/
def allBases (p : Program) (d : Ty) : List Ty := p.allBasesWithin p.length d

/-- `subobjectWithin p fuel b d v`: the base class subobject of type `b`
of the value `v`, whose declared class is `d`, within `fuel` steps of
direct derivation. A class value lists its direct base subobjects
first, in the order the class declares its bases, so the `k`th direct
base's subobject is the `k`th entry, and the search passes the declared
base along rather than reading a class name off the subobject. The
result is the one such subobject; two, as with two `b` subobjects along
different paths, or none, is `none`. -/
def subobjectWithin (p : Program) : Nat → Ty → Ty → Val → Option Val
  | 0, _, _, _ => none
  | fuel + 1, b, d, v =>
    if d == b then some v
    else
      match v with
      | .obj _ subs =>
        match ((p.directBases d).zip ((Val.toList subs).getD [])).filterMap
            (fun x => p.subobjectWithin fuel b x.1 x.2) with
        | [w] => some w
        | _ => none
      | _ => none

/-- The base class subobject of type `b` of a class value: what
`constexpr T v = A;` copies when `A`'s class derives from `T`. -/
@[std rule "temp.arg.nontype#3.sentence-1"]
def subobject (p : Program) (b : Ty) : Val → Option Val
  | .obj d subs => p.subobjectWithin p.length b (.named d) (.obj d subs)
  | _ => none

/-- `cv1 T1` is reference-compatible with `cv2 T2` when a pointer to
`cv2 T2` converts to a pointer to `cv1 T1`: `T2` is `T1` or derived from
it, and `cv1` is at least `cv2`. -/
@[std rule "dcl.init.ref#4.sentence-2"]
def referenceCompatible (p : Program) (t₁ t₂ : Ty) : Bool :=
  (t₂.stripConst == t₁.stripConst || p.derives t₂.stripConst t₁.stripConst) &&
    (!(t₂ matches .const _) || t₁ matches .const _)

end Program

/-- The rank of a standard conversion sequence the fragment forms.
Promotion needs arithmetic types, which the fragment lacks. -/
inductive ConvRank where
  /-- The identity conversion. -/
  | exactMatch
  /-- A derived-to-base conversion. -/
  | conversion
  deriving Repr, DecidableEq, Inhabited

/-- An Exact Match is a better conversion than a Conversion. -/
@[std rule "over.ics.rank#4.sentence-1"]
def ConvRank.better : ConvRank → ConvRank → Bool
  | .exactMatch, .conversion => true
  | _, _ => false

/-- How a reference parameter binds. -/
structure Binding where
  /-- An rvalue reference, rather than an lvalue reference. -/
  rvalueRef : Bool
  /-- The referenced type, with its qualifier. -/
  referred : Ty
  deriving Repr, DecidableEq, Inhabited

/-- A standard conversion sequence, as far as ranking needs one: its rank,
its cv-unqualified source and target types, and the reference binding it
includes, if any. -/
structure StdConv where
  rank : ConvRank
  source : Ty
  target : Ty
  binding : Option Binding := none
  deriving Repr, DecidableEq, Inhabited

namespace Program

/-- The conversion from a class type to a class type: the identity
conversion when they are the same, and a derived-to-base conversion, of
Conversion rank, when the target is a base of the source. -/
@[std rule "over.best.ics.general#7"]
def baseConv (p : Program) (src tgt : Ty) : Option ConvRank :=
  if src == tgt then some .exactMatch
  else if p.derives src tgt then some .conversion
  else none

/-- Whether a reference parameter can bind the argument at all: an lvalue
reference other than to const binds no rvalue, and an rvalue reference
binds no lvalue. Any other parameter is not a reference. -/
@[std rule "over.ics.ref#3.sentence-1"]
def canBind (a : CallArg) : Ty → Bool
  | .lref (.const _) => true
  | .lref _ => a.lvalue
  | .rref _ => !a.lvalue
  | _ => true

/-- The implicit conversion sequence from an argument to a parameter. A
reference binds directly when the referenced type is reference-compatible
with the argument's, and the sequence is then the identity or a
derived-to-base conversion ([over.ics.ref]/1). A parameter that is not a
reference is copy-initialized, and top-level cv-qualifiers are ignored
([over.best.ics.general]/7). -/
@[std rule "over.ics.ref#1"]
def ics (p : Program) (a : CallArg) (t : Ty) : Option StdConv :=
  let src := a.ty.referred.stripConst
  match t with
  | .lref u | .rref u =>
    if canBind a t && p.referenceCompatible u a.ty.referred then
      (p.baseConv src u.stripConst).map fun rank =>
        { rank, source := src, target := u.stripConst
          binding := some { rvalueRef := t matches .rref _, referred := u } }
    else none
  | _ => (p.baseConv src t.stripConst).map fun rank =>
      { rank, source := src, target := t.stripConst }

/-- The first tier: the subsequence rule, where the identity is a
subsequence of any non-identity sequence, then rank, then, between two
Conversions, the derived-to-base rules. For `C` derived from `B` derived
from `A`, `C` to `B` is better than `C` to `A`, and `B` to `A` is better
than `C` to `A`. -/
@[std rule "over.ics.rank#4"]
def byRank (p : Program) (s₁ s₂ : StdConv) : Bool :=
  s₁.rank.better s₂.rank ||
    (s₁.rank == .conversion && s₂.rank == .conversion &&
      ((s₁.source == s₂.source && p.derives s₁.target s₂.target) ||
        (s₁.target == s₂.target && p.derives s₂.source s₁.source)))

/-- The second tier: `S1` binds an rvalue reference to an rvalue and `S2`
binds an lvalue reference. A reference parameter in the fragment is never
an implicit object parameter, and an rvalue reference binds only
rvalues. -/
@[std rule "over.ics.rank#3"]
def byRvalueBinding (s₁ s₂ : StdConv) : Bool :=
  match s₁.binding, s₂.binding with
  | some b₁, some b₂ => b₁.rvalueRef && !b₂.rvalueRef
  | _, _ => false

/-- The third tier: `S1` and `S2` bind references to different types `T1`
and `T2`, and `T2` is reference-compatible with `T1`: `S1` binds the less
qualified one. -/
@[std rule "over.ics.rank#3"]
def byQualification (p : Program) (s₁ s₂ : StdConv) : Bool :=
  match s₁.binding, s₂.binding with
  | some b₁, some b₂ => b₁.referred != b₂.referred && p.referenceCompatible b₂.referred b₁.referred
  | _, _ => false

end Program

/-- A lexicographic chain of rules: the first rule that holds in exactly
one direction decides. -/
def lexBetter : List (StdConv → StdConv → Bool) → StdConv → StdConv → Bool
  | [], _, _ => false
  | r :: rs, s₁, s₂ => if r s₁ s₂ = r s₂ s₁ then lexBetter rs s₁ s₂ else r s₁ s₂

namespace Program

/-- The tiers of [over.ics.rank]/3, in order. -/
def tiers (p : Program) : List (StdConv → StdConv → Bool) :=
  [p.byRank, byRvalueBinding, p.byQualification]

/-- `s₁` is a better conversion sequence than `s₂`. -/
def better (p : Program) (s₁ s₂ : StdConv) : Bool := lexBetter p.tiers s₁ s₂

end Program

/-- The specification form of `Program.better`, one constructor per tier,
each guarded by the tiers before it deciding nothing. -/
@[specification]
inductive BetterConv (p : Program) : StdConv → StdConv → Prop where
  | rank {s₁ s₂ : StdConv} :
      p.byRank s₁ s₂ = true → p.byRank s₂ s₁ = false → BetterConv p s₁ s₂
  | rvalueBinding {s₁ s₂ : StdConv} :
      p.byRank s₁ s₂ = p.byRank s₂ s₁ →
      Program.byRvalueBinding s₁ s₂ = true → Program.byRvalueBinding s₂ s₁ = false →
      BetterConv p s₁ s₂
  | qualification {s₁ s₂ : StdConv} :
      p.byRank s₁ s₂ = p.byRank s₂ s₁ →
      Program.byRvalueBinding s₁ s₂ = Program.byRvalueBinding s₂ s₁ →
      p.byQualification s₁ s₂ = true → p.byQualification s₂ s₁ = false →
      BetterConv p s₁ s₂

attribute [std rule "over.ics.rank#4"] BetterConv.rank
attribute [std rule "over.ics.rank#3"] BetterConv.rvalueBinding
attribute [std rule "over.ics.rank#3"] BetterConv.qualification

/-- The function and the specification agree. -/
theorem better_iff (p : Program) (s₁ s₂ : StdConv) :
    p.better s₁ s₂ = true ↔ BetterConv p s₁ s₂ := by
  constructor
  · intro h
    simp only [Program.better, Program.tiers, lexBetter] at h
    by_cases h₁ : p.byRank s₁ s₂ = p.byRank s₂ s₁
    · rw [ite_eq_left h₁] at h
      by_cases h₂ : Program.byRvalueBinding s₁ s₂ = Program.byRvalueBinding s₂ s₁
      · rw [ite_eq_left h₂] at h
        by_cases h₃ : p.byQualification s₁ s₂ = p.byQualification s₂ s₁
        · rw [ite_eq_left h₃] at h; cases h
        · rw [ite_eq_right h₃] at h
          exact .qualification h₁ h₂ h (by rw [h] at h₃; simpa using Ne.symm h₃)
      · rw [ite_eq_right h₂] at h
        exact .rvalueBinding h₁ h (by rw [h] at h₂; simpa using Ne.symm h₂)
    · rw [ite_eq_right h₁] at h
      exact .rank h (by rw [h] at h₁; simpa using Ne.symm h₁)
  · intro h
    simp only [Program.better, Program.tiers, lexBetter]
    cases h with
    | rank h₁ h₂ => rw [ite_eq_right (by rw [h₁, h₂]; decide)]; exact h₁
    | rvalueBinding h₁ h₂ h₃ =>
      rw [ite_eq_left h₁, ite_eq_right (by rw [h₂, h₃]; decide)]; exact h₂
    | qualification h₁ h₂ h₃ h₄ =>
      rw [ite_eq_left h₁, ite_eq_left h₂, ite_eq_right (by rw [h₃, h₄]; decide)]; exact h₃

theorem lexBetter_asymm (rs : List (StdConv → StdConv → Bool)) (s₁ s₂ : StdConv) :
    lexBetter rs s₁ s₂ = true → lexBetter rs s₂ s₁ = false := by
  induction rs with
  | nil => intro h; cases h
  | cons r rs ih =>
    intro h
    simp only [lexBetter] at h ⊢
    by_cases hr : r s₁ s₂ = r s₂ s₁
    · rw [ite_eq_left hr] at h
      rw [ite_eq_left hr.symm]
      exact ih h
    · rw [ite_eq_right hr] at h
      rw [ite_eq_right (Ne.symm hr)]
      rw [h] at hr
      simpa using Ne.symm hr

/-- Better conversion sequence is asymmetric, whatever the program's class
hierarchy: no sequence is both better and worse than another
([over.ics.rank]/1). -/
@[std theorem "over.ics.rank#1.sentence-1"]
theorem better_asymm (p : Program) (s₁ s₂ : StdConv) :
    p.better s₁ s₂ = true → p.better s₂ s₁ = false :=
  lexBetter_asymm p.tiers s₁ s₂

theorem better_irrefl (p : Program) (s : StdConv) : p.better s s = false := by
  cases h : p.better s s with
  | false => rfl
  | true => have := better_asymm p s s h; rw [h] at this; cases this

/-- The ranking a program defines: conversion sequences by `Program.ics`,
compared by `Program.better`. -/
def Program.ranking (p : Program) : Ranking StdConv :=
  { ics := fun a t => .ok (p.ics a t)
    better := p.better }

end Overload
