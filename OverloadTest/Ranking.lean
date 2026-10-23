-- OverloadTest/Ranking.lean                                          -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of the program's ranking: derivation, conversion sequences and
their comparison, on the class chain `C : B : A`. -/

open Overload

private def A : Ty := .named "A"
private def B : Ty := .named "B"
private def C : Ty := .named "C"
private def p : Program := [.class "A", .class "B" [.named "A"], .class "C" [.named "B"]]

private def conv (a : CallArg) (t : Ty) : Option StdConv := p.standardIcs a t

-- Derivation is direct or indirect, and not reflexive.
#guard p.derives C A && p.derives C B && p.derives B A
#guard !p.derives A C && !p.derives A A

-- The identity and derived-to-base conversions, by value.
#guard (conv { ty := C } C).map (·.rank) == some .exactMatch
#guard (conv { ty := C } A).map (·.rank) == some .conversion
#guard (conv { ty := A } C).isNone

-- Reference binding: an lvalue reference to non-const binds no rvalue and
-- no const lvalue; an rvalue reference binds no lvalue.
#guard (conv { ty := B } (.lref B)).isNone
#guard (conv { ty := B } (.lref (.const B))).isSome
#guard (conv { ty := .const B, lvalue := true } (.lref B)).isNone
#guard (conv { ty := B, lvalue := true } (.rref B)).isNone
#guard (conv { ty := C, lvalue := true } (.lref A)).map (·.rank) == some .conversion

-- C to B is better than C to A, and B to A is better than C to A.
#guard match conv { ty := C } B, conv { ty := C } A with
  | some s₁, some s₂ => p.better s₁ s₂ && !p.better s₂ s₁
  | _, _ => false
#guard match conv { ty := B } A, conv { ty := C } A with
  | some s₁, some s₂ => p.better s₁ s₂ && !p.better s₂ s₁
  | _, _ => false

-- An rvalue reference beats an lvalue reference for an rvalue; the less
-- qualified reference beats the more qualified for an lvalue; a value and
-- a const reference are indistinguishable.
#guard match conv { ty := B } (.rref (.const B)), conv { ty := B } (.lref (.const B)) with
  | some s₁, some s₂ => p.better s₁ s₂ && !p.better s₂ s₁
  | _, _ => false
#guard match conv { ty := B, lvalue := true } (.lref B),
    conv { ty := B, lvalue := true } (.lref (.const B)) with
  | some s₁, some s₂ => p.better s₁ s₂ && !p.better s₂ s₁
  | _, _ => false
#guard match conv { ty := B, lvalue := true } B, conv { ty := B, lvalue := true } (.lref (.const B)) with
  | some s₁, some s₂ => !p.better s₁ s₂ && !p.better s₂ s₁
  | _, _ => false

-- A cyclic hierarchy, which no program can declare, decides nothing.
private def cyclic : Program := [.class "P" [.named "Q"], .class "Q" [.named "P"]]
#guard match cyclic.standardIcs { ty := .named "P" } (.named "Q"), cyclic.standardIcs { ty := .named "P" } (.named "P") with
  | some s₁, some s₂ => !cyclic.better s₁ s₁ && (cyclic.better s₂ s₁ && !cyclic.better s₁ s₂)
  | _, _ => false

-- The candidate user-defined conversions, by initialization context:
-- `S` converts to `D` by a conversion function and to `B` by an explicit
-- one; `B` has a converting constructor from `S` and `A` an explicit one.
private def S : Ty := .named "S"
private def D : Ty := .named "D"
private def q : Program :=
  p ++ [ .class "S", .class "D" [B]
       , .converting B (.constructor (.lref (.const S)))
       , .converting A (.constructor S true)
       , .converting S (.function D), .converting S (.function B true) ]
#guard q.userConversions .copy B S == [(B, .constructor (.lref (.const S))), (S, .function D)]
#guard q.userConversions .direct B S ==
  [(B, .constructor (.lref (.const S))), (S, .function D), (S, .function B true)]
#guard q.userConversions .copy A S == [(S, .function D)]
#guard q.userConversions .direct A S ==
  [(A, .constructor S true), (S, .function D), (S, .function B true)]
#guard q.userConversions .copy D S == [(S, .function D)]
#guard q.userConversions .copy C S == []
#guard q.userConversions .copy (.named "int") S == []
#guard q.userConversions .copy B A == [(B, .constructor (.lref (.const S)))]
#guard (Decl.converting B (.function D)).name? == none
#guard (Decl.converting B (.function D)).linkage == .none

-- The user-defined sequences. `S` to `B`: the constructor, whose second
-- sequence is the identity, beats the conversion function to `D`, whose
-- second is derived-to-base; `S` to `D` has one candidate; the explicit
-- constructor of `A` is a candidate only for direct-initialization, where
-- it wins on its second sequence.
private def sArg : CallArg := { ty := S }
#guard match q.ics .copy sArg B with
  | some (.userDefined f (c, .constructor ..) s) => c == B && f.rank == .exactMatch && s.rank == .exactMatch
  | _ => false
#guard match q.ics .copy sArg D with
  | some (.userDefined _ (c, .function t _ _) _) => c == S && t == D
  | _ => false
#guard match q.ics .copy sArg A with
  | some (.userDefined _ (_, .function ..) s) => s.rank == .conversion
  | _ => false
#guard match q.ics .direct sArg A with
  | some (.userDefined _ (_, .constructor _ true) _) => true
  | _ => false
-- The converted temporary binds a const lvalue reference or an rvalue
-- reference, never an lvalue reference to non-const.
#guard (q.ics .copy sArg (.lref B)).isNone
#guard (q.ics .copy sArg (.lref (.const B))).isSome
#guard (q.ics .copy sArg (.rref B)).isSome
-- A related class never goes through a user-defined conversion.
#guard match q.ics .copy { ty := D } B with | some (.standard s) => s.rank == .conversion | _ => false
#guard (q.ics .copy { ty := B } (.lref B)).isNone
#guard (q.ics .copy sArg C).isNone
-- Two candidates neither better than the other: the ambiguous sequence,
-- which ranks as a user-defined one and is indistinguishable from any.
private def r : Program :=
  p ++ [ .class "S", .converting B (.constructor (.lref (.const S))), .converting S (.function B) ]
#guard r.ics .copy sArg B == some .ambiguous
#guard match r.ics .copy sArg B, q.ics .copy sArg D with
  | some u, some v => !r.betterIcs u v && !r.betterIcs v u
  | _, _ => false
-- A standard sequence beats every user-defined one; through one
-- conversion, the better second sequence decides.
#guard match q.ics .copy { ty := D } B, q.ics .copy sArg B with
  | some u, some v => q.betterIcs u v && !q.betterIcs v u
  | _, _ => false
#guard match q.ics .copy sArg D, q.ics .copy sArg B with
  | some u, some v => !q.betterIcs u v && !q.betterIcs v u
  | _, _ => false
#guard match q.userSequence sArg D S (.function D), q.userSequence sArg A S (.function D) with
  | some u, some v => q.betterIcs u v && !q.betterIcs v u
  | _, _ => false
-- The draft's example of the ambiguous conversion sequence
-- ([over.best.ics.general]/12): `b` converts to `A` by a constructor or a
-- non-const conversion function, indistinguishably.
private def draftAmbiguous : Program :=
  [ .class "B", .class "A", .class "C"
  , .converting (.named "A") (.constructor (.lref (.named "B")))
  , .converting (.named "B") (.function (.named "A") false false)
  , .converting (.named "C") (.constructor (.lref (.named "B"))) ]
private def bLvalue : CallArg := { ty := .named "B", lvalue := true }
#guard draftAmbiguous.ics .copy bLvalue (.named "A") == some .ambiguous
#guard match draftAmbiguous.ics .copy bLvalue (.named "C") with
  | some (.userDefined ..) => true | _ => false
-- A const conversion function binds a const object; a non-const one does
-- not, and nor does a constructor taking a reference to non-const.
#guard (q.ics .copy { ty := .const S, lvalue := true } D).isSome
#guard (draftAmbiguous.ics .copy { ty := .const (.named "B"), lvalue := true } (.named "A")).isNone
