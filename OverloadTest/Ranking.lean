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

private def conv (a : CallArg) (t : Ty) : Option StdConv := p.ics a t

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
#guard match cyclic.ics { ty := .named "P" } (.named "Q"), cyclic.ics { ty := .named "P" } (.named "P") with
  | some s₁, some s₂ => !cyclic.better s₁ s₁ && (cyclic.better s₂ s₁ && !cyclic.better s₁ s₂)
  | _, _ => false
