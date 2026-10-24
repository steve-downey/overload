-- OverloadTest/Laws.lean                                             -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of the typeclass laws as semantic requirements, and of what the
headline theorems owe. -/

open Overload Overload.Typeclass

#guard lawfulConcepts.laws "Functor" == [functorIdentity, functorComposition]
#guard (lawfulConcepts.laws "Applicative").length == 4
#guard (lawfulConcepts.laws "Monad").contains superclassAgreement

-- The headline theorems of lookup owe no law; the superclass-coherence
-- theorem owes its law and the Monad concept's.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for t in [``Overload.coherence, ``Overload.stability, ``Overload.Typeclass.call_stability,
            ``Overload.inheritance_erasure, ``Overload.Typeclass.superclass_identity] do
    unless (Overload.Lint.owes env t).isEmpty do throwError "{t} should owe no law"
  let owed := Overload.Lint.owes env ``Overload.Typeclass.superclass_coherence_owed
  unless owed.contains ``Overload.Typeclass.superclassAgreement do
    throwError "superclass_coherence_owed should owe the superclass agreement"
  unless owed.contains ``Overload.Typeclass.functorIdentity do
    throwError "superclass_coherence_owed should owe the Functor laws through Monad"
