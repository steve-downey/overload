-- Overload/Object/Access.lean                                        -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Object.Machine

/-!
# The access judgement, as a relation

The lvalue-to-rvalue conversion is the rule the object model exists to
state: what a glvalue of type `T` denoting an object `o` yields. The
machine computes it (`Machine.access`); this module transcribes it as a
relation with one cited constructor per sentence and proves the two
agree (`access_iff`), per `decisions.md#spec-style`. The other
operations of the machine are given in the executable form alone, with
their citations on the definitions.
-/

namespace Overload.Object

open Machine State

namespace Machine

/-- The lvalue-to-rvalue conversion of a glvalue of type `t` denoting
the object `o`, as a function: the part of `readThrough` after
indirection. -/
@[std rule "basic.life#8" "basic.lval#11" "basic.indet#2" "conv.lval#3"]
def access (m : Model) (s : State) (t : Ty) (o : ObjId) : Behavior (State × Value) :=
  match s.obj? o with
  | none => .undefined .noObject
  | some ob =>
    if ob.life != .alive then .undefined (if ob.unionMember then .inactiveMember else .outsideLifetime)
    else if !typeAccessible t ob.ty then .undefined .typeInaccessible
    else if !Model.isScalar t then .illFormed .notScalar
    else
      let n := scalarName t
      match decode n (bytesAt s ob.region ob.offset (integerSize n)) with
      | none => .undefined .invalidRepresentation
      | some .indeterminate =>
        if isByteType t then .defined (s, .indeterminate) else .undefined .indeterminateValue
      | some .erroneous =>
        if isByteType t then .defined (s, .erroneous)
        else .erroneous ({ s with errors := s.errors ++ [.erroneousValue] }, .erroneous) .erroneousValue
      | some v => .defined (s, v)

/-- `readThrough` is indirection followed by `access`. -/
theorem readThrough_eq (m : Model) (s : State) (p : Ptr) :
    readThrough m s p = (deref m s p >>= fun (s, o) => access m s p.ty o) := by
  unfold readThrough access
  rfl

end Machine

/-- The bytes of an object's representation of type `t`. -/
def representation (s : State) (ob : Obj) (t : Ty) : List Byte :=
  Machine.bytesAt s ob.region ob.offset (integerSize (Machine.scalarName t))

/-- The lvalue-to-rvalue conversion as a specification relation: a
glvalue of type `t` denoting object `o` in state `s` has the outcome. -/
@[specification]
inductive Access (m : Model) (s : State) (t : Ty) : ObjId → Behavior (State × Value) → Prop where
  /-- A glvalue that denotes no object of the state. -/
  | noObject {o} : s.obj? o = none → Access m s t o (.undefined .noObject)
  /-- Using a glvalue to access an object outside its lifetime is
  undefined behaviour. -/
  | outsideLifetime {o ob} : s.obj? o = some ob → ob.life ≠ .alive → ob.unionMember = false →
      Access m s t o (.undefined .outsideLifetime)
  /-- A union member that is not active is outside its lifetime, and
  the access is undefined. -/
  | inactiveMember {o ob} : s.obj? o = some ob → ob.life ≠ .alive → ob.unionMember = true →
      Access m s t o (.undefined .inactiveMember)
  /-- Accessing the stored value through a glvalue through which the
  object is not type-accessible is undefined behaviour. -/
  | typeInaccessible {o ob} : s.obj? o = some ob → ob.life = .alive →
      typeAccessible t ob.ty = false → Access m s t o (.undefined .typeInaccessible)
  /-- The fragment reads scalars alone. -/
  | notScalar {o ob} : s.obj? o = some ob → ob.life = .alive → typeAccessible t ob.ty = true →
      Model.isScalar t = false → Access m s t o (.illFormed .notScalar)
  /-- Bits that are not a valid value representation for the type. -/
  | invalidRepresentation {o ob} : s.obj? o = some ob → ob.life = .alive →
      typeAccessible t ob.ty = true → Model.isScalar t = true →
      decode (Machine.scalarName t) (representation s ob t) = none →
      Access m s t o (.undefined .invalidRepresentation)
  /-- An indeterminate value produced by an evaluation is undefined
  behaviour. -/
  | indeterminate {o ob} : s.obj? o = some ob → ob.life = .alive →
      typeAccessible t ob.ty = true → Model.isScalar t = true →
      decode (Machine.scalarName t) (representation s ob t) = some .indeterminate →
      Machine.isByteType t = false → Access m s t o (.undefined .indeterminateValue)
  /-- An indeterminate value of unsigned ordinary character type or
  `std::byte` type is produced as it is. -/
  | indeterminateByte {o ob} : s.obj? o = some ob → ob.life = .alive →
      typeAccessible t ob.ty = true → Model.isScalar t = true →
      decode (Machine.scalarName t) (representation s ob t) = some .indeterminate →
      Machine.isByteType t = true → Access m s t o (.defined (s, .indeterminate))
  /-- An erroneous value produced by an evaluation is erroneous
  behaviour, and the result is that erroneous value. -/
  | erroneous {o ob} : s.obj? o = some ob → ob.life = .alive →
      typeAccessible t ob.ty = true → Model.isScalar t = true →
      decode (Machine.scalarName t) (representation s ob t) = some .erroneous →
      Machine.isByteType t = false →
      Access m s t o (.erroneous ({ s with errors := s.errors ++ [.erroneousValue] }, .erroneous) .erroneousValue)
  /-- An erroneous value of unsigned ordinary character type or
  `std::byte` type is produced as it is, with no erroneous behaviour. -/
  | erroneousByte {o ob} : s.obj? o = some ob → ob.life = .alive →
      typeAccessible t ob.ty = true → Model.isScalar t = true →
      decode (Machine.scalarName t) (representation s ob t) = some .erroneous →
      Machine.isByteType t = true → Access m s t o (.defined (s, .erroneous))
  /-- The object is read and the result is the value it contains. -/
  | value {o ob v} : s.obj? o = some ob → ob.life = .alive →
      typeAccessible t ob.ty = true → Model.isScalar t = true →
      decode (Machine.scalarName t) (representation s ob t) = some (.int v) →
      Access m s t o (.defined (s, .int v))

attribute [std rule "basic.life#7"] Access.noObject
attribute [std rule "basic.life#8"] Access.outsideLifetime
attribute [std rule "class.union.general#2" "basic.life#8"] Access.inactiveMember
attribute [std rule "basic.lval#11"] Access.typeInaccessible
attribute [std rule "basic.lval#11"] Access.notScalar
attribute [std rule "conv.lval#3"] Access.invalidRepresentation
attribute [std rule "basic.indet#2"] Access.indeterminate Access.indeterminateByte Access.erroneous
  Access.erroneousByte
attribute [std rule "conv.lval#3"] Access.value

/-- The relation and the function agree. -/
theorem access_iff (m : Model) (s : State) (t : Ty) (o : ObjId) (b : Behavior (State × Value)) :
    Access m s t o b ↔ Machine.access m s t o = b := by
  constructor
  · intro h
    cases h with
    | noObject h => simp [Machine.access, h]
    | @outsideLifetime ob h hl hu =>
      have hl' : (ob.life != Life.alive) = true := by simpa [bne_iff_ne] using hl
      simp [Machine.access, h, hl', hu]
    | @inactiveMember ob h hl hu =>
      have hl' : (ob.life != Life.alive) = true := by simpa [bne_iff_ne] using hl
      simp [Machine.access, h, hl', hu]
    | typeInaccessible h hl ha => simp [Machine.access, h, hl, ha]
    | notScalar h hl ha hs => simp [Machine.access, h, hl, ha, hs]
    | invalidRepresentation h hl ha hs hd =>
      simp [Machine.access, h, hl, ha, hs, representation] at hd ⊢; simp [hd]
    | indeterminate h hl ha hs hd hb =>
      simp [Machine.access, h, hl, ha, hs, representation] at hd ⊢; simp [hd, hb]
    | indeterminateByte h hl ha hs hd hb =>
      simp [Machine.access, h, hl, ha, hs, representation] at hd ⊢; simp [hd, hb]
    | erroneous h hl ha hs hd hb =>
      simp [Machine.access, h, hl, ha, hs, representation] at hd ⊢; simp [hd, hb]
    | erroneousByte h hl ha hs hd hb =>
      simp [Machine.access, h, hl, ha, hs, representation] at hd ⊢; simp [hd, hb]
    | value h hl ha hs hd =>
      simp [Machine.access, h, hl, ha, hs, representation] at hd ⊢; simp [hd]
  · intro h
    subst h
    unfold Machine.access
    split
    · exact .noObject ‹_›
    · rename_i ob hob
      by_cases hl : ob.life = .alive
      · by_cases ha : typeAccessible t ob.ty = true
        · by_cases hs : Model.isScalar t = true
          · simp only [hl, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ha, Bool.not_true, hs]
            split
            · exact .invalidRepresentation hob hl ha hs (by simpa [representation] using ‹_›)
            · split
              · exact .indeterminateByte hob hl ha hs (by simpa [representation] using ‹_›) ‹_›
              · exact .indeterminate hob hl ha hs (by simpa [representation] using ‹_›)
                  (Bool.eq_false_iff.mpr ‹¬ Machine.isByteType t = true›)
            · split
              · exact .erroneousByte hob hl ha hs (by simpa [representation] using ‹_›) ‹_›
              · exact .erroneous hob hl ha hs (by simpa [representation] using ‹_›)
                  (Bool.eq_false_iff.mpr ‹¬ Machine.isByteType t = true›)
            · rename_i v hv1 hv2 heq
              cases v with
              | indeterminate => exact absurd rfl hv1
              | erroneous => exact absurd rfl hv2
              | int v => exact .value hob hl ha hs (by simpa [representation] using heq)
          · have hs' : Model.isScalar t = false := by simpa using hs
            simp only [hl, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ha, Bool.not_true, hs',
              Bool.not_false]
            exact .notScalar hob hl ha hs'
        · have ha' : typeAccessible t ob.ty = false := by simpa using ha
          simp only [hl, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ha', Bool.not_false]
          exact .typeInaccessible hob hl ha'
      · have hl' : (ob.life != Life.alive) = true := by simpa [bne_iff_ne] using hl
        simp only [hl', ↓reduceIte]
        by_cases hu : ob.unionMember = true
        · simp only [hu, ↓reduceIte]; exact .inactiveMember hob hl hu
        · have hu' : ob.unionMember = false := by simpa using hu
          simp only [hu', Bool.false_eq_true, ↓reduceIte]; exact .outsideLifetime hob hl hu'

end Overload.Object
