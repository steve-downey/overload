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

/-- The user-defined conversions declared for a class, in order. -/
def conversionsOf (p : Program) (cls : Ty) : List UserConv :=
  p.filterMap fun
    | .converting c conv => if c == cls then some conv else none
    | _ => none

end Program

/-- Is a conversion a candidate in an initialization context? An explicit
constructor is a candidate only for direct-initialization, and so is an
explicit conversion function. -/
@[std rule "over.match.ctor#1" "class.conv.fct#4"]
def UserConv.candidate (init : Init) (c : UserConv) : Bool :=
  !c.explicit || init == .direct

namespace Program

/-- The candidate user-defined conversions for initializing an object of
type `tgt` from an expression of type `src`, both without top-level
cv-qualifiers, in an initialization context: the constructors of a class
`tgt`, all of them for direct-initialization and the non-explicit ones
otherwise ([over.match.ctor]/1, [over.match.copy]/1); and, when `src` is
a class, its conversion functions to `tgt` or to a class derived from a
class `tgt` ([over.match.copy]/1), or to a non-class `tgt` itself, the
fragment's only standard conversion to one ([over.match.conv]/1).
Each is paired with the class that declares it, which is what tells two
conversions apart when sequences are ranked. -/
@[std rule "over.match.copy#1" "over.match.conv#1"]
def userConversions (p : Program) (init : Init) (tgt src : Ty) : List (Ty × UserConv) :=
  let ctors := (p.conversionsOf tgt).filterMap fun
    | c@(.constructor ..) => if c.candidate init then some (tgt, c) else none
    | _ => none
  let fns := (p.conversionsOf src).filterMap fun
    | c@(.function t _ _ _) =>
      if c.candidate init && (t == tgt || p.derives t tgt) then some (src, c) else none
    | _ => none
  ctors ++ fns

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

/-- The standard conversion sequence from an argument to a parameter, with
the reference binding it includes. A reference binds directly when the
referenced type is reference-compatible with the argument's, and the
sequence is then the identity or a derived-to-base conversion
([over.ics.ref]/1). A parameter that is not a reference is
copy-initialized, and top-level cv-qualifiers are ignored
([over.best.ics.general]/7). The user-defined sequences are formed on
top of this by `ics`. -/
@[std rule "over.ics.ref#1"]
def standardIcs (p : Program) (a : CallArg) (t : Ty) : Option StdConv :=
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

/-! ## User-defined conversion sequences -/

/-- An implicit conversion sequence: a standard conversion sequence, a
user-defined conversion sequence, or the ambiguous conversion sequence,
which stands for several well-formed sequences to one parameter. The
ellipsis conversion sequence is out of the fragment. An implicit
conversion sequence converts an argument in a function call to the type
of the corresponding parameter, as an initialization of an object or
reference by a single expression ([over.best.ics.general]/1). -/
@[std rule "over.best.ics.general#1"]
inductive Ics where
  /-- A standard conversion sequence. -/
  | standard (s : StdConv)
  /-- A user-defined conversion sequence: the standard sequence to the
  constructor's parameter or to the conversion function's object
  parameter, the conversion itself paired with the class declaring it,
  and the second standard sequence to the parameter, which includes any
  reference binding. Both parts are standard sequences, so one value
  goes through one user-defined conversion. -/
  | userDefined (first : StdConv) (via : Ty × UserConv) (second : StdConv)
  /-- The ambiguous conversion sequence. -/
  | ambiguous
  deriving Repr, DecidableEq, Inhabited

attribute [std rule "over.best.ics.general#3"] Ics.standard
attribute [std rule "over.ics.user#1" "over.ics.user#2"] Ics.userDefined
attribute [std rule "over.best.ics.general#12"] Ics.ambiguous

/-- How many user-defined conversions a sequence applies: one for a
user-defined sequence and for the ambiguous sequence, which ranks as
one. -/
def Ics.userConversions : Ics → Nat
  | .standard _ => 0
  | .userDefined .. | .ambiguous => 1

namespace Program

/-- The user-defined conversion sequence through one candidate, when its
two standard sequences form. For a constructor the first converts the
argument to the parameter and the second converts the constructed
prvalue to the target; for a conversion function the first binds the
implicit object parameter, a reference to the class, to which an rvalue
binds as an lvalue would ([over.match.funcs.general]/5), and the second
converts the prvalue result to the target. The first is formed by the
standard cases alone: no user-defined sequence is considered for the
parameter of a candidate constructor or the object parameter of a
candidate conversion function. A reference target binds the prvalue as
a temporary, so an lvalue reference to non-const forms no sequence
([over.ics.ref]/3). -/
@[std rule "over.ics.user#1" "over.best.ics.general#4" "over.best.ics.general#9"
  "over.match.funcs.general#5"]
def userSequence (p : Program) (a : CallArg) (t : Ty) (cls : Ty) (conv : UserConv) : Option Ics :=
  match conv with
  | .constructor param _ _ => do
    let first ← p.standardIcs a param
    let second ← p.standardIcs { ty := cls } t
    some (.userDefined first (cls, conv) second)
  | .function target _ const _ => do
    let first ← p.standardIcs { a with lvalue := true } (.lref (if const then .const cls else cls))
    let second ← p.standardIcs { ty := target } t
    some (.userDefined first (cls, conv) second)

/-- The user-defined sequences the candidates of an initialization form. -/
def userSequences (p : Program) (init : Init) (a : CallArg) (t : Ty) : List Ics :=
  (p.userConversions init t.referred.stripConst a.ty.referred.stripConst).filterMap fun (c, conv) =>
    p.userSequence a t c conv

/-- Is the parameter's class the argument's own, or a base of it? Such a
conversion is the identity or derived-to-base, of standard rank, and is
never user-defined, whether or not it binds. -/
@[std rule "over.ics.user#4"]
def related (p : Program) (a : CallArg) (t : Ty) : Bool :=
  let src := a.ty.referred.stripConst
  let tgt := t.referred.stripConst
  src == tgt || p.derives src tgt

/-- Among the candidates of one initialization by user-defined
conversion, chosen by overload resolution over the one argument, `u` is
the better candidate than `v`: its conversion of the argument, the first
sequence, is not worse and is better, or, if not that, its second
standard sequence to the destination is better. -/
@[std rule "dcl.init.general#15" "over.match.best.general#2"]
def betterCandidate (p : Program) : Ics → Ics → Bool
  | .userDefined f₁ _ s₁, .userDefined f₂ _ s₂ => !p.better f₂ f₁ && (p.better f₁ f₂ || p.better s₁ s₂)
  | _, _ => false

/-- Is `u` the best of the sequences: better than every other? -/
def isBest (p : Program) (us : List Ics) (u : Ics) : Bool :=
  us.all fun v => v == u || p.betterCandidate u v

/-- The best of the formed sequences: the one better than every other,
or the ambiguous conversion sequence when there are sequences and none
is best. -/
@[std rule "over.best.ics.general#12"]
def bestSequence (p : Program) (us : List Ics) : Option Ics :=
  match us with
  | [] => none
  | _ => match us.find? (p.isBest us) with
    | some u => some u
    | none => some .ambiguous

/-- The implicit conversion sequence from an argument to a parameter type
in an initialization context: the standard sequence when one forms,
which it does for the argument's own class and its bases whenever the
binding allows ([over.best.ics.general]/7, [over.ics.ref]/1); otherwise
the best user-defined sequence among the candidates, a reference
parameter binding the converted temporary ([over.ics.ref]/2). A
parameter that is not a reference models copy-initialization of the
parameter from the argument ([over.best.ics.general]/6). -/
@[std rule "over.best.ics.general#6" "over.ics.ref#2" "dcl.init.ref#5"]
def ics (p : Program) (init : Init) (a : CallArg) (t : Ty) : Option Ics :=
  match p.standardIcs a t with
  | some s => some (.standard s)
  | none => if p.related a t then none else p.bestSequence (p.userSequences init a t)

end Program

/-- The specification form of `Program.ics`: the standard sequence when
one forms; otherwise, for an unrelated class, the user-defined sequence
better than every other candidate's, or the ambiguous sequence when
there are candidates and none is best. -/
@[specification]
inductive IcsForms (p : Program) (init : Init) (a : CallArg) (t : Ty) : Ics → Prop where
  | standard {s : StdConv} : p.standardIcs a t = some s → IcsForms p init a t (.standard s)
  | userDefined {u : Ics} : p.standardIcs a t = none → p.related a t = false →
      u ∈ p.userSequences init a t →
      (∀ v ∈ p.userSequences init a t, v ≠ u → p.betterCandidate u v = true) →
      IcsForms p init a t u
  | ambiguous : p.standardIcs a t = none → p.related a t = false →
      p.userSequences init a t ≠ [] →
      (∀ u ∈ p.userSequences init a t, ∃ v ∈ p.userSequences init a t,
        v ≠ u ∧ p.betterCandidate u v = false) →
      IcsForms p init a t .ambiguous

attribute [std rule "over.best.ics.general#7"] IcsForms.standard
attribute [std rule "dcl.init.general#15"] IcsForms.userDefined
attribute [std rule "over.best.ics.general#12"] IcsForms.ambiguous

/-- The better candidate is asymmetric: the first sequences cannot each be
not worse and one better, so both seconds would be better. -/
theorem betterCandidate_asymm (p : Program) (u v : Ics) :
    p.betterCandidate u v = true → p.betterCandidate v u = false := by
  intro h
  cases u <;> cases v <;> simp only [Program.betterCandidate] at h ⊢
  rename_i f₁ _ s₁ f₂ _ s₂
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.or_eq_true] at h
  obtain ⟨h₁, h₂⟩ := h
  rcases h₂ with h₂ | h₂
  · simp [h₂]
  · cases hf : p.better f₂ f₁ with
    | true => rw [hf] at h₁; cases h₁
    | false =>
      cases hf' : p.better f₁ f₂ with
      | true => simp
      | false => simp [better_asymm p s₁ s₂ h₂]

theorem isBest_iff (p : Program) (us : List Ics) (u : Ics) :
    p.isBest us u = true ↔ ∀ v ∈ us, v ≠ u → p.betterCandidate u v = true := by
  simp only [Program.isBest, List.all_eq_true, Bool.or_eq_true, beq_iff_eq]
  constructor
  · intro h v hv hne
    rcases h v hv with h | h
    · exact absurd h hne
    · exact h
  · intro h v hv
    by_cases hvu : v = u
    · exact .inl hvu
    · exact .inr (h v hv hvu)

/-- The best sequence of a non-empty list is the first best one, or the
ambiguous sequence. -/
theorem bestSequence_eq (p : Program) (us : List Ics) (hne : us ≠ []) :
    p.bestSequence us = match us.find? (p.isBest us) with
      | some u => some u
      | none => some .ambiguous := by
  cases us with
  | nil => exact absurd rfl hne
  | cons x xs => rfl

/-- The function and the specification agree. -/
theorem ics_iff (p : Program) (init : Init) (a : CallArg) (t : Ty) (u : Ics) :
    p.ics init a t = some u ↔ IcsForms p init a t u := by
  constructor
  · intro h
    simp only [Program.ics] at h
    cases hs : p.standardIcs a t with
    | some s => rw [hs] at h; cases h; exact .standard hs
    | none =>
      rw [hs] at h
      cases hr : p.related a t with
      | true => rw [hr] at h; cases h
      | false =>
        rw [hr] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        have hne : p.userSequences init a t ≠ [] := by
          intro h0; rw [h0] at h; simp [Program.bestSequence] at h
        rw [bestSequence_eq p _ hne] at h
        cases hf : (p.userSequences init a t).find? (p.isBest (p.userSequences init a t)) with
        | some w =>
          rw [hf] at h; cases h
          exact .userDefined hs hr (List.mem_of_find?_eq_some hf)
            ((isBest_iff p _ _).mp (List.find?_some hf))
        | none =>
          rw [hf] at h; cases h
          refine .ambiguous hs hr hne fun w hw => ?_
          have hnb : p.isBest (p.userSequences init a t) w = false := by
            simpa using List.find?_eq_none.mp hf w hw
          simp only [Program.isBest, List.all_eq_false, Bool.or_eq_true, beq_iff_eq, not_or,
            Bool.not_eq_true] at hnb
          obtain ⟨v, hv, hvw, hb⟩ := hnb
          exact ⟨v, hv, hvw, hb⟩
  · intro h
    cases h with
    | standard hs => simp [Program.ics, hs]
    | userDefined hs hr hu hb =>
      simp only [Program.ics, hs, hr, Bool.false_eq_true, ↓reduceIte]
      have hne : p.userSequences init a t ≠ [] := fun h => by rw [h] at hu; cases hu
      rw [bestSequence_eq p _ hne]
      cases hf : (p.userSequences init a t).find? (p.isBest (p.userSequences init a t)) with
      | some w =>
        have hw := List.mem_of_find?_eq_some hf
        have hbw := (isBest_iff p _ w).mp (List.find?_some hf)
        by_cases hwu : w = u
        · rw [hwu]
        · have h₁ := hb w hw hwu
          have h₂ := hbw u hu (Ne.symm hwu)
          have := betterCandidate_asymm p u w h₁
          rw [h₂] at this; cases this
      | none => exact absurd ((isBest_iff p _ u).mpr hb) (List.find?_eq_none.mp hf u hu)
    | ambiguous hs hr hne hb =>
      simp only [Program.ics, hs, hr, Bool.false_eq_true, ↓reduceIte]
      rw [bestSequence_eq p _ hne]
      cases hf : (p.userSequences init a t).find? (p.isBest (p.userSequences init a t)) with
      | some w =>
        obtain ⟨v, hv, hvw, hbv⟩ := hb w (List.mem_of_find?_eq_some hf)
        have := (isBest_iff p _ w).mp (List.find?_some hf) v hv hvw
        rw [hbv] at this; cases this
      | none => rfl

/-- A standard sequence that forms is the sequence: the user-defined
cases are reached only when none does, so every call the standard
sequences decide keeps its outcome. -/
@[simp]
theorem ics_standard (p : Program) (init : Init) (a : CallArg) (t : Ty) (s : StdConv)
    (h : p.standardIcs a t = some s) : p.ics init a t = some (.standard s) := by
  simp [Program.ics, h]

/-- At most one user-defined conversion is applied to one value: a
sequence's parts are standard sequences, so it applies one or none. -/
@[std theorem "class.conv.general#4"]
theorem ics_one_user_defined (p : Program) (init : Init) (a : CallArg) (t : Ty) (u : Ics)
    (_ : p.ics init a t = some u) : u.userConversions ≤ 1 := by
  cases u <;> simp [Ics.userConversions]

/-- A program without user-defined conversions forms only standard
sequences. -/
def Program.conversionFree (p : Program) : Bool :=
  p.all fun | .converting .. => false | _ => true

theorem userConversions_free (p : Program) (h : p.conversionFree = true) (init : Init) (tgt src : Ty) :
    p.userConversions init tgt src = [] := by
  have hc : ∀ c, p.conversionsOf c = [] := by
    intro c
    simp only [Program.conversionsOf, List.filterMap_eq_nil_iff]
    intro d hd
    simp only [Program.conversionFree, List.all_eq_true] at h
    have := h d hd
    cases d <;> simp_all
  simp [Program.userConversions, hc]

theorem ics_free (p : Program) (h : p.conversionFree = true) (init : Init) (a : CallArg) (t : Ty) :
    p.ics init a t = (p.standardIcs a t).map .standard := by
  simp only [Program.ics]
  cases p.standardIcs a t with
  | some s => rfl
  | none =>
    simp only [Program.userSequences, userConversions_free p h, List.filterMap_nil,
      Program.bestSequence, Option.map_none]
    split <;> rfl

/-- An explicit constructor or conversion function is no candidate for
copy-initialization, so no implicit conversion sequence, which models
the copy-initialization of a parameter from an argument, goes through
one. -/
@[std theorem "over.match.copy#1"]
theorem explicit_never_implicit (p : Program) (a : CallArg) (t : Ty) (f s : StdConv)
    (c : Ty) (conv : UserConv) (h : p.ics .copy a t = some (.userDefined f (c, conv) s)) :
    conv.explicit = false := by
  have h' := (ics_iff p .copy a t _).mp h
  cases h' with
  | userDefined _ _ hu _ =>
    simp only [Program.userSequences, List.mem_filterMap] at hu
    obtain ⟨⟨c', conv'⟩, hc, hs⟩ := hu
    have hconv : conv' = conv := by
      cases conv' with
      | constructor param e =>
        simp only [Program.userSequence] at hs
        cases h₁ : p.standardIcs a param with
        | none => simp [h₁] at hs
        | some first =>
          cases h₂ : p.standardIcs { ty := c' } t with
          | none => simp [h₁, h₂] at hs
          | some second =>
            simp [h₁, h₂] at hs
            exact hs.2.1.2
      | function tgt e cst =>
        simp only [Program.userSequence] at hs
        cases h₁ : p.standardIcs { a with lvalue := true } (.lref (if cst then .const c' else c')) with
        | none => simp [h₁] at hs
        | some first =>
          cases h₂ : p.standardIcs { ty := tgt } t with
          | none => simp [h₁, h₂] at hs
          | some second =>
            simp [h₁, h₂] at hs
            exact hs.2.1.2
    have hcand : conv'.candidate .copy = true := by
      simp only [Program.userConversions, List.mem_append, List.mem_filterMap] at hc
      rcases hc with ⟨x, _, hx⟩ | ⟨x, _, hx⟩ <;> split at hx <;> simp at hx <;>
        (obtain ⟨_, _, rfl⟩ := hx; simp_all)
    rw [← hconv]
    simpa [UserConv.candidate] using hcand

/-! ## The candidate initializer of a class-typed constant parameter -/

namespace Program

/-- The one value of a class in the fragment, within `fuel` steps of
derivation: a class value lists its base subobjects and nothing else,
so every object of a class is template-argument-equivalent to this one,
whichever constructor made it. -/
def uniqueValueWithin (p : Program) : Nat → Ty → Val
  | 0, .named n => .obj' n []
  | fuel + 1, .named n => .obj' n ((p.directBases (.named n)).map (p.uniqueValueWithin fuel))
  | _, _ => .obj' "" []

/-- The one value of a class in the fragment. -/
def uniqueValue (p : Program) (t : Ty) : Val := p.uniqueValueWithin p.length t

/-- The value of the candidate initializer `v` of `constexpr T v = A;`
for a class value `A`: the value itself for its own class and its `T`
base subobject for a derived class, when the standard sequence forms;
the object a converting constructor or conversion function makes when
the copy-initialization goes through a user-defined conversion
sequence, which in the fragment is the class's one value; and none when
no sequence forms or the sequence is ambiguous, which makes the
template-id invalid. -/
@[std rule "temp.arg.nontype#3" "dcl.init.general#15"]
def candidateInitializer (p : Program) (t : Ty) : Val → Option Val
  | .obj d subs =>
    match p.ics .copy { ty := .named d } t with
    | some (.standard _) => p.subobject t (.obj d subs)
    | some (.userDefined ..) => some (p.uniqueValue t)
    | _ => none
  | _ => none

end Program

/-- Through a user-defined conversion sequence the candidate initializer
is the class's one value, whatever the source. -/
theorem candidateInitializer_user (p : Program) (t : Ty) (d : String) (subs : Val)
    (f s : StdConv) (v : Ty × UserConv)
    (h : p.ics .copy { ty := .named d } t = some (.userDefined f v s)) :
    p.candidateInitializer t (.obj d subs) = some (p.uniqueValue t) := by
  simp [Program.candidateInitializer, h]

/-- In a program without user-defined conversions the candidate
initializer is the base subobject, when the derived-to-base conversion
exists. -/
theorem candidateInitializer_free (p : Program) (h : p.conversionFree = true) (c d : String)
    (subs : Val) :
    p.candidateInitializer (.named c) (.obj d subs) =
      match p.baseConv (.named d) (.named c) with
      | some _ => p.subobject (.named c) (.obj d subs)
      | none => none := by
  simp only [Program.candidateInitializer, ics_free p h, Program.standardIcs, Ty.referred,
    Ty.stripConst]
  cases p.baseConv (.named d) (.named c) <;> rfl

/-! ## Ranking implicit conversion sequences -/

namespace Program

/-- `u₁` is a better conversion sequence than `u₂`. A standard sequence is
better than a user-defined one and than the ambiguous sequence, which
ranks as one ([over.ics.rank]/2). Two standard sequences compare by
`better`. Two user-defined sequences compare only when they contain the
same conversion, by their second standard sequences ([over.ics.rank]/3),
and the ambiguous sequence is indistinguishable from every user-defined
one ([over.best.ics.general]/12). -/
@[std rule "over.ics.rank#2" "over.ics.rank#3"]
def betterIcs (p : Program) : Ics → Ics → Bool
  | .standard s₁, .standard s₂ => p.better s₁ s₂
  | .standard _, _ => true
  | .userDefined _ v₁ s₁, .userDefined _ v₂ s₂ => v₁ == v₂ && p.better s₁ s₂
  | _, _ => false

end Program

/-- The specification form of `Program.betterIcs`, one constructor per
rule. -/
@[specification]
inductive BetterIcs (p : Program) : Ics → Ics → Prop where
  /-- Two standard sequences compare as standard sequences. -/
  | standard {s₁ s₂ : StdConv} : BetterConv p s₁ s₂ → BetterIcs p (.standard s₁) (.standard s₂)
  /-- A standard sequence is better than a user-defined sequence. -/
  | form {s : StdConv} {u : Ics} : u.userConversions = 1 → BetterIcs p (.standard s) u
  /-- Through the same conversion, the better second standard sequence. -/
  | userDefined {f₁ f₂ s₁ s₂ : StdConv} {v : Ty × UserConv} :
      BetterConv p s₁ s₂ → BetterIcs p (.userDefined f₁ v s₁) (.userDefined f₂ v s₂)

attribute [std rule "over.ics.rank#3"] BetterIcs.standard
attribute [std rule "over.ics.rank#2"] BetterIcs.form
attribute [std rule "over.ics.rank#3"] BetterIcs.userDefined

/-- The function and the specification agree. -/
theorem betterIcs_iff (p : Program) (u₁ u₂ : Ics) :
    p.betterIcs u₁ u₂ = true ↔ BetterIcs p u₁ u₂ := by
  constructor
  · intro h
    match u₁, u₂ with
    | .standard s₁, .standard s₂ => exact .standard ((better_iff p _ _).mp h)
    | .standard _, .userDefined .. => exact .form rfl
    | .standard _, .ambiguous => exact .form rfl
    | .userDefined _ v₁ s₁, .userDefined _ v₂ s₂ =>
      simp only [Program.betterIcs, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      exact .userDefined ((better_iff p _ _).mp h)
    | .userDefined .., .standard _ | .userDefined .., .ambiguous | .ambiguous, _ =>
      simp [Program.betterIcs] at h
  · intro h
    cases h with
    | standard h => exact (better_iff p _ _).mpr h
    | form h => cases ‹Ics› <;> simp_all [Ics.userConversions, Program.betterIcs]
    | userDefined h => simp [Program.betterIcs, (better_iff p _ _).mpr h]

/-- Better implicit conversion sequence is asymmetric ([over.ics.rank]/1). -/
@[std theorem "over.ics.rank#1.sentence-1"]
theorem betterIcs_asymm (p : Program) (u₁ u₂ : Ics) :
    p.betterIcs u₁ u₂ = true → p.betterIcs u₂ u₁ = false := by
  intro h
  match u₁, u₂ with
  | .standard s₁, .standard s₂ => exact better_asymm p _ _ h
  | .standard _, .userDefined .. | .standard _, .ambiguous => simp [Program.betterIcs]
  | .userDefined _ v₁ s₁, .userDefined _ v₂ s₂ =>
    simp only [Program.betterIcs, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    simp [Program.betterIcs, better_asymm p _ _ h]
  | .userDefined .., .standard _ | .userDefined .., .ambiguous | .ambiguous, _ =>
    simp [Program.betterIcs] at h

/-- A standard conversion sequence is a better conversion sequence than
any user-defined one, and than the ambiguous sequence, whatever the
sequences convert. -/
@[std theorem "over.ics.rank#2"]
theorem standard_beats_user_defined (p : Program) (s : StdConv) (u : Ics)
    (h : u.userConversions = 1) : p.betterIcs (.standard s) u = true :=
  (betterIcs_iff p _ _).mpr (.form h)

theorem betterIcs_irrefl (p : Program) (u : Ics) : p.betterIcs u u = false := by
  cases h : p.betterIcs u u with
  | false => rfl
  | true => have := betterIcs_asymm p u u h; rw [h] at this; cases this

/-- The ranking a program defines: implicit conversion sequences by
`Program.ics`, in the copy-initialization context of argument passing,
compared by `Program.betterIcs`. -/
@[std rule "dcl.init.general#13"]
def Program.ranking (p : Program) : Ranking Ics :=
  { ics := fun a t => .ok (p.ics .copy a t)
    better := p.betterIcs }

end Overload
