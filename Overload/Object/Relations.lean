-- Overload/Object/Relations.lean                                     -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Object.Access

/-!
# The machine's rules as relations

`decisions.md#spec-style` gives each mechanism twice, as a relation with
one cited constructor per sentence and as a function, with an agreement
theorem. The machine's operations started as functions alone, with the
access judgement the exception (`Overload/Object/Access.lean`). This
module gives the rest of the lifetime rules their relation forms:

* `Deref`, indirection ([expr.unary.op]/1, [basic.life]/7,
  [basic.compound]/6);
* `Destroy`, destruction through a pointer ([class.dtor]/16, /18);
* `WriteTail` and `Write`, assignment ([basic.lval]/10, /11,
  [dcl.type.cv]/4, [class.union.general]/5);
* `Reuse`, storage reuse by a creation ([basic.life]/2, /12,
  [intro.object]/2, /3);
* `CreateAfter` and `CreateObject`, creation ([basic.life]/10,
  [intro.object]/16, [dcl.init.general]/8).

At the leaves a relation uses the executable parts that are definitions
and not rules, as `Overload/Specs.lean` does: `pointAt`, the implicit
creation of [intro.object]/13 and `decisions.md#implicit-creation`;
`unionActivation`; `reuseState`; `applyInit`. What is left to the
constructors is the case analysis, which is where the sentences are.
-/

namespace Overload.Object

open Machine State

@[simp] theorem Behavior.bind_defined {α β : Type} (a : α) (f : α → Behavior β) :
    (Behavior.defined a >>= f) = f a := rfl
@[simp] theorem Behavior.pure_defined {α : Type} (a : α) : (pure a : Behavior α) = .defined a := rfl
@[simp] theorem Behavior.bind_undefined {α β : Type} (w : Why) (f : α → Behavior β) :
    (Behavior.undefined w >>= f) = .undefined w := rfl
@[simp] theorem Behavior.bind_illFormed {α β : Type} (w : Why) (f : α → Behavior β) :
    (Behavior.illFormed w >>= f) = .illFormed w := rfl

/-! ## Indirection -/

/-- The glvalue a pointer forms. -/
@[specification]
inductive Deref (m : Model) (s : State) (p : Ptr) : Behavior (State × ObjId) → Prop where
  /-- A pointer to an object denotes that object, or the one that
  transparently replaced it. -/
  | object {o} : p.loc = .object o →
      Deref m s p (.defined (s.touch (s.resolve o), s.resolve o))
  /-- A pointer into storage that is no longer allocated is not valid. -/
  | unallocated {r off} : p.loc = .storage r off → allocated s r off 0 = false →
      Deref m s p (.undefined .invalidPointer)
  /-- A pointer into allocated storage denotes the object of the
  pointer's type found or implicitly created there. -/
  | found {r off s' o} : p.loc = .storage r off → allocated s r off 0 = true →
      pointAt m s p.ty r off = (s', some o) → Deref m s p (.defined (s'.touch o, o))
  /-- And refers to no object when there is none. -/
  | missing {r off s'} : p.loc = .storage r off → allocated s r off 0 = true →
      pointAt m s p.ty r off = (s', none) → Deref m s p (.undefined .noObject)
  /-- Indirection through the null pointer value. -/
  | null : p.loc = .null → Deref m s p (.undefined .nullPointer)
  /-- Indirection through an invalid pointer value. -/
  | invalid : p.loc = .invalid → Deref m s p (.undefined .invalidPointer)

attribute [std rule "expr.unary.op#1" "basic.life#10"] Deref.object
attribute [std rule "basic.compound#6"] Deref.unallocated Deref.invalid
attribute [std rule "basic.life#7" "intro.object#14"] Deref.found
attribute [std rule "basic.life#7"] Deref.missing
attribute [std rule "expr.unary.op#1"] Deref.null

theorem deref_agrees (m : Model) (s : State) (p : Ptr) (b : Behavior (State × ObjId)) :
    Deref m s p b ↔ deref m s p = b := by
  constructor
  · intro h
    cases h with
    | object h => simp [deref, h]
    | unallocated h ha => simp [deref, h, ha]
    | found h ha hp => simp [deref, h, ha, hp]
    | missing h ha hp => simp [deref, h, ha, hp]
    | null h => simp [deref, h]
    | invalid h => simp [deref, h]
  · intro h
    subst h
    unfold deref
    cases hl : p.loc with
    | object o => simp only [hl]; exact .object hl
    | storage r off =>
      simp only [hl]
      by_cases ha : allocated s r off 0 = true
      · have ha' : (!allocated s r off 0) = false := by simp [ha]
        rw [if_neg (by simp [ha])]
        rcases hp : pointAt m s p.ty r off with ⟨s', _ | o⟩
        · exact .missing hl ha hp
        · exact .found hl ha hp
      · have ha' : allocated s r off 0 = false := by simpa using ha
        rw [if_pos (by simp [ha'])]
        exact .unallocated hl ha'
    | null => simp only [hl]; exact .null hl
    | invalid => simp only [hl]; exact .invalid hl

/-- Indirection is defined or undefined, never erroneous or ill-formed. -/
theorem deref_shape (m : Model) (s : State) (p : Ptr) :
    (∃ x, deref m s p = .defined x) ∨ ∃ w, deref m s p = .undefined w := by
  have h : Deref m s p (deref m s p) := (deref_agrees m s p _).mpr rfl
  generalize deref m s p = b at h
  cases h <;> first | exact .inl ⟨_, rfl⟩ | exact .inr ⟨_, rfl⟩

/-! ## Destruction -/

/-- Destruction through a pointer. -/
@[specification]
inductive Destroy (m : Model) (s : State) (p : Ptr) : Behavior State → Prop where
  /-- The pointer denotes nothing usable. -/
  | derefUndefined {w} : Deref m s p (.undefined w) → Destroy m s p (.undefined w)
  /-- No object of the state. -/
  | noObject {s' o} : Deref m s p (.defined (s', o)) → s'.obj? o = none →
      Destroy m s p (.undefined .noObject)
  /-- The destructor is specified by a type-name denoting the destructor's
  class; invoking it for an object not of that class is undefined
  ([class.dtor]/16). -/
  | wrongClass {s' o ob} : Deref m s p (.defined (s', o)) → s'.obj? o = some ob →
      ob.ty.stripConst ≠ p.ty.stripConst → Destroy m s p (.undefined .wrongDestructor)
  /-- Invoked for an object whose lifetime has ended: undefined
  ([class.dtor]/18). -/
  | ended {s' o ob} : Deref m s p (.defined (s', o)) → s'.obj? o = some ob →
      ob.ty.stripConst = p.ty.stripConst → ob.life ≠ .alive →
      Destroy m s p (.undefined .destructorOutsideLifetime)
  /-- Once a destructor is invoked the object's lifetime ends
  ([class.dtor]/18). -/
  | destroyed {s' o ob} : Deref m s p (.defined (s', o)) → s'.obj? o = some ob →
      ob.ty.stripConst = p.ty.stripConst → ob.life = .alive →
      Destroy m s p (.defined (s'.endLifetime o))

attribute [std rule "class.dtor#16"] Destroy.wrongClass
attribute [std rule "class.dtor#18"] Destroy.ended Destroy.destroyed
attribute [std rule "basic.life#7"] Destroy.derefUndefined Destroy.noObject

theorem destroy_agrees (m : Model) (s : State) (p : Ptr) (b : Behavior State) :
    Destroy m s p b ↔ destroyThrough m s p = b := by
  constructor
  · intro h
    cases h with
    | derefUndefined hd => simp [destroyThrough, (deref_agrees ..).mp hd]
    | noObject hd ho => simp [destroyThrough, (deref_agrees ..).mp hd, ho]
    | wrongClass hd ho hne =>
      simp [destroyThrough, (deref_agrees ..).mp hd, ho, bne_iff_ne, hne]
    | ended hd ho he hl =>
      simp [destroyThrough, (deref_agrees ..).mp hd, ho, he, hl]
    | destroyed hd ho he hl =>
      simp [destroyThrough, (deref_agrees ..).mp hd, ho, he, hl]
  · intro h
    subst h
    rcases deref_shape m s p with ⟨⟨s', o⟩, hd⟩ | ⟨w, hd⟩
    · have hr : Deref m s p (.defined (s', o)) := (deref_agrees ..).mpr hd
      unfold destroyThrough
      rw [hd]
      simp only [Behavior.bind_defined]
      rcases ho : s'.obj? o with _ | ob
      · exact .noObject hr ho
      · simp only []
        by_cases he : ob.ty.stripConst = p.ty.stripConst
        · by_cases hl : ob.life = .alive
          · simp [he, hl]; exact .destroyed hr ho he hl
          · simp [he, hl]; exact .ended hr ho he hl
        · simp [bne_iff_ne, he]; exact .wrongClass hr ho he
    · have hr : Deref m s p (.undefined w) := (deref_agrees ..).mpr hd
      unfold destroyThrough
      rw [hd]
      exact .derefUndefined hr

/-! ## Assignment -/

/-- The tail of an assignment, once the glvalue denotes an object within
its lifetime. -/
@[specification]
inductive WriteTail (m : Model) (s : State) (p : Ptr) (o : ObjId) (ob : Obj) (v : Int) :
    Behavior State → Prop where
  /-- Accessing the stored value through a glvalue through which the
  object is not type-accessible is undefined. -/
  | typeInaccessible : typeAccessible p.ty ob.ty = false → WriteTail m s p o ob v (.undefined .typeInaccessible)
  /-- Any attempt to modify a const object during its lifetime is
  undefined, and so is modifying a const subobject. -/
  | modifiesConst : typeAccessible p.ty ob.ty = true →
      (ob.isConst = true ∨ (s.obj? (s.completeObject o)).any Obj.isConst = true) →
      WriteTail m s p o ob v (.undefined .modifiesConst)
  /-- The fragment assigns scalars. -/
  | notScalar : typeAccessible p.ty ob.ty = true → ob.isConst = false →
      (s.obj? (s.completeObject o)).any Obj.isConst = false → Model.isScalar p.ty = false →
      WriteTail m s p o ob v (.illFormed .notScalar)
  /-- Otherwise the object's bytes are the value's representation. -/
  | scalar : typeAccessible p.ty ob.ty = true → ob.isConst = false →
      (s.obj? (s.completeObject o)).any Obj.isConst = false → Model.isScalar p.ty = true →
      WriteTail m s p o ob v
        (.defined (writeBytes s ob.region ob.offset (encode v (integerSize (scalarName p.ty)))))

attribute [std rule "basic.lval#11"] WriteTail.typeInaccessible WriteTail.notScalar
attribute [std rule "dcl.type.cv#4"] WriteTail.modifiesConst
attribute [std rule "conv.lval#3" "basic.indet#1"] WriteTail.scalar

theorem writeTail_agrees (m : Model) (s : State) (p : Ptr) (o : ObjId) (ob : Obj) (v : Int)
    (b : Behavior State) : WriteTail m s p o ob v b ↔ writeTail m s p o ob v = b := by
  constructor
  · intro h
    cases h with
    | typeInaccessible h => simp [writeTail, h]
    | modifiesConst h hc =>
      rcases hc with hc | hc <;> simp [writeTail, h, hc]
    | notScalar h hc1 hc2 hs => simp [writeTail, h, hc1, hc2, hs]
    | scalar h hc1 hc2 hs => simp [writeTail, h, hc1, hc2, hs]
  · intro h
    subst h
    unfold writeTail
    by_cases ha : typeAccessible p.ty ob.ty = true
    · by_cases hc : (ob.isConst || (s.obj? (s.completeObject o)).any Obj.isConst) = true
      · rw [if_neg (by simp [ha]), if_pos hc]
        exact .modifiesConst ha (by simpa using hc)
      · have hc' : ob.isConst = false ∧ (s.obj? (s.completeObject o)).any Obj.isConst = false := by
          simpa [Bool.or_eq_true] using hc
        by_cases hs : Model.isScalar p.ty = true
        · rw [if_neg (by simp [ha]), if_neg hc, if_neg (by simp [hs])]
          exact .scalar ha hc'.1 hc'.2 hs
        · have hs' : Model.isScalar p.ty = false := by simpa using hs
          rw [if_neg (by simp [ha]), if_neg hc, if_pos (by simp [hs'])]
          exact .notScalar ha hc'.1 hc'.2 hs'
    · have ha' : typeAccessible p.ty ob.ty = false := by simpa using ha
      rw [if_pos (by simp [ha'])]
      exact .typeInaccessible ha'

/-- Assignment through a pointer. -/
@[specification]
inductive Write (m : Model) (s : State) (p : Ptr) (v : Int) : Behavior State → Prop where
  /-- A modifiable lvalue's type is not const-qualified; modifying through
  a const glvalue is ill-formed. -/
  | constGlvalue : p.ty.isConst = true → Write m s p v (.illFormed .constGlvalue)
  | derefUndefined {w} : p.ty.isConst = false → Deref m s p (.undefined w) → Write m s p v (.undefined w)
  | noObject {s' o} : p.ty.isConst = false → Deref m s p (.defined (s', o)) → s'.obj? o = none →
      Write m s p v (.undefined .noObject)
  /-- The glvalue denotes an object within its lifetime. -/
  | alive {s' o ob b} : p.ty.isConst = false → Deref m s p (.defined (s', o)) → s'.obj? o = some ob →
      ob.life = .alive → WriteTail m s' p o ob v b → Write m s p v b
  /-- An assignment to a union member of scalar or trivially
  default-constructible type begins its lifetime, and ends the lifetime of
  the other members. -/
  | activated {s' o ob u b} : p.ty.isConst = false → Deref m s p (.defined (s', o)) →
      s'.obj? o = some ob → ob.life ≠ .alive → unionActivation m s' o = some u →
      WriteTail m (activate s' u) p o ob v b → Write m s p v b
  /-- Otherwise a member that is not active is outside its lifetime. -/
  | inactive {s' o ob} : p.ty.isConst = false → Deref m s p (.defined (s', o)) →
      s'.obj? o = some ob → ob.life ≠ .alive → unionActivation m s' o = none → ob.unionMember = true →
      Write m s p v (.undefined .inactiveMember)
  /-- Modification of an object outside its lifetime is undefined. -/
  | outside {s' o ob} : p.ty.isConst = false → Deref m s p (.defined (s', o)) →
      s'.obj? o = some ob → ob.life ≠ .alive → unionActivation m s' o = none → ob.unionMember = false →
      Write m s p v (.undefined .outsideLifetime)

attribute [std rule "basic.lval#10"] Write.constGlvalue
attribute [std rule "basic.life#7"] Write.derefUndefined Write.noObject
attribute [std rule "basic.life#8"] Write.alive Write.outside
attribute [std rule "class.union.general#5"] Write.activated
attribute [std rule "class.union.general#2" "basic.life#8"] Write.inactive

theorem write_agrees (m : Model) (s : State) (p : Ptr) (v : Int) (b : Behavior State) :
    Write m s p v b ↔ writeThrough m s p v = b := by
  constructor
  · intro h
    cases h with
    | constGlvalue hc => simp [writeThrough, hc]
    | derefUndefined hc hd => simp [writeThrough, hc, (deref_agrees ..).mp hd]
    | noObject hc hd ho => simp [writeThrough, hc, (deref_agrees ..).mp hd, ho]
    | alive hc hd ho hl ht =>
      simp [writeThrough, hc, (deref_agrees ..).mp hd, ho, hl, (writeTail_agrees ..).mp ht]
    | activated hc hd ho hl hu ht =>
      simp [writeThrough, hc, (deref_agrees ..).mp hd, ho, hl, hu, (writeTail_agrees ..).mp ht]
    | inactive hc hd ho hl hu hm => simp [writeThrough, hc, (deref_agrees ..).mp hd, ho, hl, hu, hm]
    | outside hc hd ho hl hu hm => simp [writeThrough, hc, (deref_agrees ..).mp hd, ho, hl, hu, hm]
  · intro h
    subst h
    by_cases hc : p.ty.isConst = true
    · unfold writeThrough; simp only [hc, if_true]; exact .constGlvalue hc
    · have hc' : p.ty.isConst = false := by simpa using hc
      rcases deref_shape m s p with ⟨⟨s', o⟩, hd⟩ | ⟨w, hd⟩
      · have hr : Deref m s p (.defined (s', o)) := (deref_agrees ..).mpr hd
        unfold writeThrough
        rw [if_neg hc, hd]
        simp only [Behavior.bind_defined]
        rcases ho : s'.obj? o with _ | ob
        · exact .noObject hc' hr ho
        · simp only []
          by_cases hl : ob.life = .alive
          · simp only [hl, beq_self_eq_true, if_true, pure]
            exact .alive hc' hr ho hl ((writeTail_agrees ..).mpr rfl)
          · have hl' : (ob.life == .alive) = false := by simpa using hl
            rcases hu : unionActivation m s' o with _ | u
            · by_cases hm : ob.unionMember = true
              · simp [hl', hu, hm]; exact .inactive hc' hr ho hl hu hm
              · have hm' : ob.unionMember = false := by simpa using hm
                simp [hl', hu, hm']; exact .outside hc' hr ho hl hu hm'
            · simp [hl', hu, pure]
              exact .activated hc' hr ho hl hu ((writeTail_agrees ..).mpr rfl)
      · have hr : Deref m s p (.undefined w) := (deref_agrees ..).mpr hd
        unfold writeThrough
        rw [if_neg hc, hd]
        exact .derefUndefined hc' hr

/-! ## Storage reuse -/

/-- Creating an object reuses the storage of the objects it overlaps. -/
@[specification]
inductive Reuse (m : Model) (s : State) (ty : Ty) (r : RegionId) (off : Nat) :
    Behavior (State × Option ObjId) → Prop where
  /-- Creating a new object within the storage that a const, complete
  object with static, thread, or automatic storage duration occupies
  results in undefined behaviour. -/
  | constStorage : reuseConstComplete m s ty r off = true → Reuse m s ty r off (.undefined .constStorageReuse)
  /-- Otherwise the lifetime of each overlapped object ends unless it
  survives, and the new object's parent is the containing object of the
  subobject it corresponds to, if any. -/
  | reused {parent} : reuseConstComplete m s ty r off = false → reuseParent m s ty r off = parent →
      Reuse m s ty r off (.defined (reuseState m s ty r off, parent))

attribute [std rule "basic.life#12"] Reuse.constStorage
attribute [std rule "basic.life#2" "intro.object#2" "intro.object#3"] Reuse.reused

theorem reuse_agrees (m : Model) (s : State) (ty : Ty) (r : RegionId) (off : Nat)
    (b : Behavior (State × Option ObjId)) : Reuse m s ty r off b ↔ reuse m s ty r off = b := by
  constructor
  · intro h
    cases h with
    | constStorage hc => simp [reuse, hc]
    | reused hc hp => simp [reuse, hc, hp]
  · intro h
    subst h
    unfold reuse
    by_cases hc : reuseConstComplete m s ty r off = true
    · rw [if_pos hc]; exact .constStorage hc
    · have hc' : reuseConstComplete m s ty r off = false := by simpa using hc
      rw [if_neg hc]; exact .reused hc' rfl

/-- Reuse never fails in any way but the const rule. -/
theorem reuse_shape (m : Model) (s : State) (ty : Ty) (r : RegionId) (off : Nat) :
    (∃ x, reuse m s ty r off = .defined x) ∨ reuse m s ty r off = .undefined .constStorageReuse := by
  unfold reuse
  by_cases hc : reuseConstComplete m s ty r off = true
  · exact .inr (by rw [if_pos hc])
  · exact .inl ⟨_, by rw [if_neg hc]⟩

/-! ## Creation -/

/-- Creation once the storage has been reused. -/
@[specification]
inductive CreateAfter (m : Model) (s : State) (ty : Ty) (r : RegionId) (off : Nat) (init : Init) (count : Nat)
    (parent : Option ObjId) : Behavior (State × ObjId) → Prop where
  /-- A class with a constructor body is left under construction;
  `construct` initializes it. -/
  | underConstruction {s₂ o} : underConstruction m ty init count = true →
      create m s ty count r off parent .constructing = (s₂, o) →
      CreateAfter m s ty r off init count parent (.defined (linkReplacements s₂ o, o))
  /-- The beginning of the lifetime of an array of `unsigned char`
  implicitly creates objects within it, and value-initialization zeroes
  it. -/
  | byteArray {s₂ o} : underConstruction m ty init count = false → (count != 1) = true →
      create m s ty count r off parent .alive = (s₂, o) →
      CreateAfter m s ty r off init count parent
        (.defined (byteBufferState m (linkReplacements s₂ o) ty r off init count o, o))
  /-- Otherwise the object is initialized. -/
  | initialized {s₂ o b} : underConstruction m ty init count = false → (count != 1) = false →
      create m s ty count r off parent .alive = (s₂, o) →
      applyInit m (linkReplacements s₂ o) o ty r off init = b →
      CreateAfter m s ty r off init count parent (b >>= fun s' => .defined (s', o))

attribute [std rule "class.base.init#11" "basic.life#10"] CreateAfter.underConstruction
attribute [std rule "intro.object#16"] CreateAfter.byteArray
attribute [std rule "dcl.init.general#8" "basic.life#2"] CreateAfter.initialized

theorem createAfter_agrees (m : Model) (s : State) (ty : Ty) (r : RegionId) (off : Nat) (init : Init)
    (count : Nat) (parent : Option ObjId) (b : Behavior (State × ObjId)) :
    CreateAfter m s ty r off init count parent b ↔ createAfter m s ty r off init count parent = b := by
  constructor
  · intro h
    cases h with
    | underConstruction hu hc => simp [createAfter, hu, hc]
    | byteArray hu hn hc => simp [createAfter, hu, hn, hc]
    | initialized hu hn hc hi =>
      have hn' : count = 1 := by simpa using hn
      subst hn'
      simp [createAfter, hu, hc, hi]
  · intro h
    subst h
    unfold createAfter
    rcases hc : create m s ty count r off parent (if underConstruction m ty init count then .constructing else .alive)
      with ⟨s₂, o⟩
    by_cases hu : underConstruction m ty init count = true
    · simp only [hu, ite_true] at hc ⊢
      exact .underConstruction hu hc
    · have hu' : underConstruction m ty init count = false := by simpa using hu
      simp only [hu', Bool.false_eq_true, ite_false] at hc ⊢
      by_cases hn : (count != 1) = true
      · rw [if_pos hn]
        exact .byteArray hu' hn hc
      · have hn' : (count != 1) = false := by simpa using hn
        rw [if_neg hn]
        exact .initialized hu' hn' hc rfl

/-- Creation of an object in storage already obtained. -/
@[specification]
inductive CreateObject (m : Model) (s : State) (ty : Ty) (r : RegionId) (off : Nat) (init : Init) (count : Nat) :
    Behavior (State × ObjId) → Prop where
  /-- The region must be allocated and hold the object. -/
  | unallocated : allocated s r off (count * m.sizeOf ty) = false →
      CreateObject m s ty r off init count (.undefined .lifetimePrecondition)
  /-- Creation within the storage of a const complete object. -/
  | reuseUndefined {w} : allocated s r off (count * m.sizeOf ty) = true →
      Reuse m s ty r off (.undefined w) → CreateObject m s ty r off init count (.undefined w)
  /-- Creation after the storage has been reused. -/
  | afterReuse {s₁ parent b} : allocated s r off (count * m.sizeOf ty) = true →
      Reuse m s ty r off (.defined (s₁, parent)) → CreateAfter m s₁ ty r off init count parent b →
      CreateObject m s ty r off init count b

attribute [std rule "obj.lifetime#4"] CreateObject.unallocated
attribute [std rule "basic.life#12"] CreateObject.reuseUndefined
attribute [std rule "basic.life#2"] CreateObject.afterReuse

theorem createObject_agrees (m : Model) (s : State) (ty : Ty) (r : RegionId) (off : Nat) (init : Init)
    (count : Nat) (b : Behavior (State × ObjId)) :
    CreateObject m s ty r off init count b ↔ createObject m s ty r off init count = b := by
  constructor
  · intro h
    cases h with
    | unallocated ha => simp [createObject, ha]
    | reuseUndefined ha hr => simp [createObject, ha, (reuse_agrees ..).mp hr]
    | afterReuse ha hr hc => simp [createObject, ha, (reuse_agrees ..).mp hr, (createAfter_agrees ..).mp hc]
  · intro h
    subst h
    unfold createObject
    by_cases ha : allocated s r off (count * m.sizeOf ty) = true
    · rw [if_neg (by simp [ha])]
      rcases reuse_shape m s ty r off with ⟨⟨s₁, parent⟩, hr⟩ | hr
      · have hrr : Reuse m s ty r off (.defined (s₁, parent)) := (reuse_agrees ..).mpr hr
        rw [hr]
        simp only [Behavior.bind_defined]
        exact .afterReuse ha hrr ((createAfter_agrees ..).mpr rfl)
      · have hrr : Reuse m s ty r off (.undefined .constStorageReuse) := (reuse_agrees ..).mpr hr
        rw [hr]
        exact .reuseUndefined ha hrr
    · have ha' : allocated s r off (count * m.sizeOf ty) = false := by simpa using ha
      rw [if_pos (by simp [ha'])]
      exact .unallocated ha'

end Overload.Object
