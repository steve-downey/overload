-- Overload/Traits.lean                                               -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Special

/-!
# Type traits as judgements of a program

`Program.trait` answers every `Trait` the fragment can state. The
structural ones are `Trait.answer`, from the types alone. The rest are
the program's: `is_base_of` through its derivation, `is_convertible`
through its implicit conversion sequences ([meta.rel]/6),
`is_constructible` and `is_assignable` through overload resolution over
a class's constructors and assignment operators with the usable-candidate
check ([meta.unary.prop]/9, [over.match.general]/4), `is_destructible`
and the `is_trivially_` forms through the special member functions,
`is_trivially_copyable` and `is_standard_layout` through [class.prop],
`is_empty` through the members, `is_polymorphic`, `is_abstract` and
`has_virtual_destructor` through the virtual functions. So a trait's answer is a theorem of the
rules it rests on, and the differential tests compare it with the
compilers' own trait.

What stays with the oracle is the residue of `decisions.md#trait-residue`:
a conversion between two different non-class types, which the fragment's
sequences do not form, and `is_invocable` of a class callee, whose call
is resolved above the environment.
-/

namespace Overload

namespace Program

/-- The argument `declval<T>()` supplies: an lvalue of `T`'s referred
type when `T` is an lvalue reference, an xvalue of it otherwise. -/
@[std rule "meta.unary.prop#4"]
def declval (t : Ty) : CallArg := { ty := t.referred, lvalue := t.isLvalueReference }

/-- A referenceable type of the fragment: an object or reference type. -/
def referenceable (t : Ty) : Bool := !t.isVoid && !t.isFunction

/-- `const T&` and `T&&` for a referenceable `T`, with reference
collapsing when `T` is a reference. -/
def constLref (t : Ty) : Ty := Ty.collapse (.lref (if t.isRef then t else .const t))
def rref (t : Ty) : Ty := Ty.collapse (.rref t)

/-! ## Convertible -/

/-- `is_convertible<From, To>`: the return statement `return
declval<From>();` of a function returning `To` is well-formed. `void` to
`void` holds and nothing else converts to or from `void`; no function
type is a return type, and no abstract class is the return type of a
function definition ([dcl.fct.def.general]/2); otherwise the copy-initialization of the returned
object or the binding of the returned reference forms an implicit
conversion sequence that is not ambiguous, and when the destination is
the argument's class or a base, the constructor it selects is usable.
A conversion between two different non-class types is outside the
fragment's sequences and is left to the oracle. -/
@[std rule "meta.rel#6" "dcl.fct.def.general#2"]
def convertible (p : Program) (from_ to : Ty) : Subst Bool :=
  if to.isVoid then .ok from_.isVoid
  else if from_.isVoid || to.isFunction then .ok false
  else if !to.isRef && to.stripConst.isClass && p.abstract to.stripConst then .ok false
  else
    let a := declval from_
    let src := a.ty.stripConst
    let dst := to.referred.stripConst
    if !src.isClass && !dst.isClass && src != dst then
      .soft s!"conversion between {repr src} and {repr dst} is outside the fragment"
    else
      match p.ics .copy a to with
      | none | some .ambiguous => .ok false
      | some (.standard _) => .ok (p.copyInitUsable a to)
      | some (.userDefined ..) => .ok true

/-! ## Constructible and assignable -/

/-- `is_constructible<T, Args...>`: the variable definition
`T t(declval<Args>()...);` is well-formed. A reference binds one
argument; no object of an abstract class is defined ([basic.def]/5); a
class resolves its constructors for direct-initialization and the
candidate must be usable; a scalar is value-initialized by no
argument and initialized by one of its own type or of a class with a
conversion function to it. No `void` or function type is constructible. -/
@[std rule "meta.unary.prop#9" "over.match.general#4" "basic.def#5"]
def constructible (p : Program) (t : Ty) (args : List Ty) : Subst Bool :=
  let as := args.map declval
  if t.isVoid || t.isFunction then .ok false
  else if t.isRef then
    match as with
    | [a] => .ok (match p.ics .direct a t with | some .ambiguous | none => false | some _ => true)
    | _ => .ok false
  else if t.stripConst.isClass then
    .ok (!p.abstract t.stripConst &&
      usable p.facts t.stripConst (resolveCtor p.facts p .direct t.stripConst as))
  else
    match as with
    | [] => .ok true
    | [a] =>
      if a.ty.stripConst == t.stripConst then .ok true
      else if a.ty.stripConst.isClass then
        .ok (match p.ics .direct a t with | some (.userDefined ..) => true | _ => false)
      else .soft s!"conversion between {repr a.ty} and {repr t} is outside the fragment"
    | _ => .ok false

/-- `is_assignable<T, U>`: `declval<T>() = declval<U>()` is well-formed.
A class object, lvalue or xvalue, resolves its assignment operators for
the argument and the candidate must be usable; a `const` object has
none it can call; a scalar is assignable only as a non-`const` lvalue,
from its own type or a class with a conversion function to it. -/
@[std rule "meta.unary.prop#5" "over.match.general#4"]
def assignable (p : Program) (t u : Ty) : Subst Bool :=
  let obj := t.referred
  if obj.isVoid || obj.isFunction then .ok false
  else if obj.isConst then .ok false
  else
    let c := obj.stripConst
    let a := declval u
    if c.isClass then .ok (usable p.facts c (resolveAssign p.facts p c a))
    else if !t.isLvalueReference then .ok false
    else if a.ty.stripConst == c then .ok true
    else if a.ty.stripConst.isClass then
      .ok (match p.ics .copy a c with | some (.userDefined ..) => true | _ => false)
    else .soft s!"conversion between {repr a.ty} and {repr c} is outside the fragment"

/-- `is_destructible<T>`: a reference, or a complete object type whose
destructor is not deleted. -/
@[std rule "meta.unary.prop#5"]
def destructible (p : Program) (t : Ty) : Bool :=
  if t.isRef then true
  else if t.isVoid || t.isFunction then false
  else if t.stripConst.isClass then !p.isDeleted t.stripConst .dtor
  else true

/-! ## Trivially -/

/-- Constructible, and the initialization is known to call no operation
that is not trivial: for a class, the constructor selected is a special
member and trivial; a scalar's or a reference's initialization is
trivial. -/
@[std rule "meta.unary.prop#5"]
def triviallyConstructible (p : Program) (t : Ty) (args : List Ty) : Subst Bool := do
  if !(← p.constructible t args) then return false
  if t.stripConst.isClass && !t.isRef then
    match resolveCtor p.facts p .direct t.stripConst (args.map declval) with
    | .selected (_, some k) => return p.trivial t.stripConst k
    | _ => return false
  else return true

/-- Assignable, and the assignment calls nothing that is not trivial. -/
@[std rule "meta.unary.prop#5"]
def triviallyAssignable (p : Program) (t u : Ty) : Subst Bool := do
  if !(← p.assignable t u) then return false
  let c := t.referred.stripConst
  if c.isClass then
    match resolveAssign p.facts p c (declval u) with
    | .selected (_, some k) => return p.trivial c k
    | _ => return false
  else return true

/-- Destructible, and the destructor is trivial. -/
@[std rule "meta.unary.prop#5"]
def triviallyDestructible (p : Program) (t : Ty) : Bool :=
  p.destructible t && (!t.stripConst.isClass || t.isRef || p.trivial t.stripConst .dtor)

/-! ## Properties of classes -/

/-- A trivially copyable class: at least one eligible copy or move
constructor or assignment operator, each eligible one trivial, and a
trivial non-deleted destructor. -/
@[std rule "class.prop#1"]
def triviallyCopyableClass (p : Program) (c : Ty) : Bool :=
  let ks := [SmfKind.copyCtor, .moveCtor, .copyAssign, .moveAssign]
  ks.any (p.eligible c) && ks.all (fun k => !p.eligible c k || p.trivial c k) &&
    p.trivial c .dtor && !p.isDeleted c .dtor

/-- `M(X)` of [class.prop]/2 within `fuel`: the types of the subobjects
that can be at offset zero in `X`. A class with no members has none; one
with members has its first member's type and that type's own. -/
@[std rule "class.prop#2"]
def zeroOffsetWithin (p : Program) : Nat → Ty → List Ty
  | 0, _ => []
  | fuel + 1, c =>
    match (p.membersOf c).head? with
    | none => []
    | some m =>
      let t := m.ty.stripConst
      t :: (if t.isClass then p.zeroOffsetWithin fuel t else [])

/-- A standard-layout class within `fuel`, the bullets of [class.prop]/2
on the fragment: no virtual functions; no member of reference type or of
a non-standard-layout class; every base standard-layout; at most one
base subobject of any type; every member first declared in one class; no
base among the types at offset zero. The fragment has no virtual bases,
no bit-fields, and public members only, so the other bullets hold. -/
@[std rule "class.prop#2"]
def standardLayoutWithin (p : Program) : Nat → Ty → Bool
  | 0, _ => false
  | fuel + 1, c =>
    let members := p.membersOf c
    let all := p.allBases c
    !p.polymorphic c &&
    members.all (fun m => !m.ty.isReference &&
      (!m.ty.stripConst.isClass || p.standardLayoutWithin fuel m.ty.stripConst)) &&
    (p.directBases c).all (p.standardLayoutWithin fuel) &&
    all.eraseDups.length == all.length &&
    ((c :: all).filter fun x => !(p.membersOf x).isEmpty).length ≤ 1 &&
    (p.zeroOffsetWithin (fuel + 1) c).all fun z => !all.contains z

/-- A standard-layout class. -/
def standardLayoutClass (p : Program) (c : Ty) : Bool := p.standardLayoutWithin p.length c

/-- An empty class within `fuel`: no non-static data members, no virtual
member functions, and every base empty. -/
@[std rule "meta.unary.prop#5"]
def emptyWithin (p : Program) : Nat → Ty → Bool
  | 0, _ => false
  | fuel + 1, c =>
    !p.polymorphic c && (p.membersOf c).isEmpty && (p.directBases c).all (p.emptyWithin fuel)

/-- An empty class. -/
def emptyClass (p : Program) (c : Ty) : Bool := p.emptyWithin p.length c

/-! ## Invocable -/

/-- The function type a callee denotes, if any: the type itself or the
pointee of a pointer to function, as parameter list, return type and
exception specification. -/
def fnType (f : Ty) : Option (List Ty × Ty × Bool) :=
  match f.referred.stripConst with
  | .fn ps r ne => ps.toList.map fun params => (params, r, ne)
  | .ptr (.fn ps r ne) => ps.toList.map fun params => (params, r, ne)
  | _ => none

/-- `is_invocable<Fn, Args...>` for a function type or a pointer to one:
each argument has an implicit conversion sequence to the parameter, and
the arities agree. A class callee is a call on an object, resolved
above the environment, and is left to the oracle. -/
@[std rule "meta.rel#3"]
def invocable (p : Program) (f : Ty) (args : List Ty) : Subst Bool :=
  match fnType f with
  | some (params, _, _) =>
    if params.length != args.length then .ok false
    else
      match conversions p.ranking (args.map declval) params with
      | .ok (some cs) => .ok (cs.all (· != .ambiguous))
      | .ok none => .ok false
      | .soft r => .soft r
      | .hard r => .hard r
  | none =>
    if f.referred.stripConst.isClass then
      .soft s!"is_invocable of a class callee is resolved above the environment"
    else .ok false

/-! ## Known not to throw -/

/-- Does the user-defined conversion of an implicit conversion sequence
throw? A standard sequence invokes no function. -/
@[std rule "except.spec#6"]
def icsThrowing : Option Ics → Bool
  | some (.userDefined _ (_, conv) _) => conv.throwing
  | _ => false

/-- `is_nothrow_constructible<T, Args...>`: constructible, and the
variable definition is known not to throw: for a class, the constructor
resolution selects is non-throwing and so is the initialization of each
of its parameters from the arguments; for a reference or a scalar, the
one conversion invoked, if user-defined, is non-throwing. -/
@[std rule "meta.unary.prop#5" "except.spec#6"]
def nothrowConstructible (p : Program) (t : Ty) (args : List Ty) : Subst Bool := do
  if !(← p.constructible t args) then return false
  let as := args.map declval
  if t.isRef then
    match as with
    | [a] => return !icsThrowing (p.ics .direct a t)
    | _ => return false
  else if t.stripConst.isClass then
    let c := t.stripConst
    match resolveCtor p.facts p .direct c as with
    | .selected (cand, k) =>
      return !p.selectedCtorThrowing p.throwing c (.selected (cand, k)) &&
        !(as.zip cand.params).any fun (a, pt) => p.initThrowing a pt
    | _ => return false
  else
    match as with
    | [a] => return !icsThrowing (p.ics .direct a t)
    | _ => return true

/-- `is_nothrow_assignable<T, U>`: assignable, and the assignment is
known not to throw: the operator resolution selects is non-throwing and
so is its parameter's initialization; a scalar's assignment invokes at
most a conversion function. -/
@[std rule "meta.unary.prop#5" "except.spec#6"]
def nothrowAssignable (p : Program) (t u : Ty) : Subst Bool := do
  if !(← p.assignable t u) then return false
  let c := t.referred.stripConst
  let a := declval u
  if c.isClass then
    match resolveAssign p.facts p c a with
    | .selected (cand, some k) =>
      return !p.throwing c k && !([a].zip cand.params).any fun (a, pt) => p.initThrowing a pt
    | _ => return false
  else return !icsThrowing (p.ics .copy a c)

/-- `is_nothrow_destructible<T>`: destructible, and the destructor is
non-throwing. -/
@[std rule "meta.unary.prop#5"]
def nothrowDestructible (p : Program) (t : Ty) : Bool :=
  p.destructible t && (t.isRef || !t.stripConst.isClass || !p.throwing t.stripConst .dtor)

/-- `is_nothrow_convertible<From, To>`: convertible, and the conversion,
the return statement of [meta.rel]/6, is known not to throw. -/
@[std rule "meta.rel#6" "except.spec#6"]
def nothrowConvertible (p : Program) (from_ to : Ty) : Subst Bool := do
  if !(← p.convertible from_ to) then return false
  if to.isVoid then return true
  return !p.initThrowing (declval from_) to

/-- `is_nothrow_invocable<Fn, Args...>` for a function type or a pointer
to one: invocable, the type's exception specification non-throwing, and
each parameter's initialization known not to throw. -/
@[std rule "meta.rel#3" "except.spec#6"]
def nothrowInvocable (p : Program) (f : Ty) (args : List Ty) : Subst Bool := do
  if !(← p.invocable f args) then return false
  match fnType f with
  | some (params, _, ne) =>
    return ne && !((args.map declval).zip params).any fun (a, pt) => p.initThrowing a pt
  | none => return false

/-- `is_nothrow_swappable<T>`: `swap(declval<T&>(), declval<T&>())` is
well-formed and known not to throw. With no `swap` the program declares,
the call selects `std::swap`, whose exception specification is
`is_nothrow_move_constructible_v<T> && is_nothrow_move_assignable_v<T>`
and whose constraints are the two base traits; a program that declares a
`swap` of its own is resolved above the environment and is left to the
oracle. -/
@[std rule "meta.unary.prop#5" "utility.swap#4" "concept.swappable#2"]
def nothrowSwappable (p : Program) (t : Ty) : Subst Bool := do
  let obj := t.referred
  if obj.isVoid || obj.isFunction then return false
  if !(p.candidates "swap").isEmpty then
    Subst.soft "is_nothrow_swappable with a user swap is resolved above the environment"
  else
    let mc ← p.nothrowConstructible obj [rref obj]
    let ma ← p.nothrowAssignable (Ty.collapse (.lref obj)) (rref obj)
    return mc && ma

/-! ## The program's answer -/

/-- The program's answer to a trait on its arguments, once substituted:
the structural answer for a structural trait, and otherwise the
judgements above, on concrete types. -/
@[std rule "meta.unary.cat#3" "meta.unary.comp#2" "meta.unary.prop#5" "meta.rel#3"]
def trait (p : Program) (q : Trait) (args : List Ty) : Subst Bool :=
  if q.structural then Trait.answer q args
  else if !args.all Ty.concrete then .soft s!"{q.spelling} of a dependent type"
  else
    let onClass (t : Ty) (f : Ty → Bool) (other : Bool) : Subst Bool :=
      .ok (if t.stripConst.isClass && !t.isRef then f t.stripConst else other)
    match q, args with
    | .isBaseOf, [b, d] =>
      let b := b.stripConst
      let d := d.stripConst
      .ok (b.isClass && d.isClass && (b == d || p.derives d b))
    | .isConvertible, [f, t] => p.convertible f t
    | .isConstructible, t :: as => p.constructible t as
    | .isDefaultConstructible, [t] => p.constructible t []
    | .isCopyConstructible, [t] => if referenceable t then p.constructible t [constLref t] else .ok false
    | .isMoveConstructible, [t] => if referenceable t then p.constructible t [rref t] else .ok false
    | .isAssignable, [t, u] => p.assignable t u
    | .isCopyAssignable, [t] =>
      if referenceable t then p.assignable (Ty.collapse (.lref t)) (constLref t) else .ok false
    | .isMoveAssignable, [t] =>
      if referenceable t then p.assignable (Ty.collapse (.lref t)) (rref t) else .ok false
    | .isDestructible, [t] => .ok (p.destructible t)
    | .isTriviallyCopyable, [t] => onClass t p.triviallyCopyableClass t.isScalar
    | .isStandardLayout, [t] => onClass t p.standardLayoutClass t.isScalar
    | .isEmpty, [t] => onClass t p.emptyClass false
    | .isTriviallyDefaultConstructible, [t] => p.triviallyConstructible t []
    | .isTriviallyCopyConstructible, [t] =>
      if referenceable t then p.triviallyConstructible t [constLref t] else .ok false
    | .isTriviallyMoveConstructible, [t] =>
      if referenceable t then p.triviallyConstructible t [rref t] else .ok false
    | .isTriviallyAssignable, [t, u] => p.triviallyAssignable t u
    | .isTriviallyCopyAssignable, [t] =>
      if referenceable t then p.triviallyAssignable (Ty.collapse (.lref t)) (constLref t) else .ok false
    | .isTriviallyMoveAssignable, [t] =>
      if referenceable t then p.triviallyAssignable (Ty.collapse (.lref t)) (rref t) else .ok false
    | .isTriviallyDestructible, [t] => .ok (p.triviallyDestructible t)
    | .isNothrowDestructible, [t] => .ok (p.nothrowDestructible t)
    | .isPolymorphic, [t] => onClass t p.polymorphic false
    | .isAbstract, [t] => onClass t p.abstract false
    | .hasVirtualDestructor, [t] => onClass t p.virtualDtor false
    | .isNothrowConstructible, t :: as => p.nothrowConstructible t as
    | .isNothrowDefaultConstructible, [t] => p.nothrowConstructible t []
    | .isNothrowCopyConstructible, [t] =>
      if referenceable t then p.nothrowConstructible t [constLref t] else .ok false
    | .isNothrowMoveConstructible, [t] =>
      if referenceable t then p.nothrowConstructible t [rref t] else .ok false
    | .isNothrowAssignable, [t, u] => p.nothrowAssignable t u
    | .isNothrowCopyAssignable, [t] =>
      if referenceable t then p.nothrowAssignable (Ty.collapse (.lref t)) (constLref t) else .ok false
    | .isNothrowMoveAssignable, [t] =>
      if referenceable t then p.nothrowAssignable (Ty.collapse (.lref t)) (rref t) else .ok false
    | .isNothrowSwappable, [t] => p.nothrowSwappable t
    | .isNothrowConvertible, [f, t] => p.nothrowConvertible f t
    | .isInvocable, f :: as => p.invocable f as
    | .isNothrowInvocable, f :: as => p.nothrowInvocable f as
    | q, _ => .soft s!"{q.spelling}: wrong number of arguments"

end Program

/-- A flat class, one with no declared special member, conversion, base,
class-typed member or default member initializer, has non-throwing
special members: each is implicitly declared and invokes nothing. -/
@[std theorem "except.spec#7" "except.spec#8" "except.spec#9"]
theorem implicit_noexcept_from_subobjects (p : Program) (c : Ty) (hc : p.flatClass c = true)
    (hl : 0 < p.length) (k : SmfKind) : p.throwing c k = false := by
  simp only [Program.flatClass, Bool.and_eq_true, List.isEmpty_iff] at hc
  obtain ⟨⟨⟨hs, hconv⟩, hb⟩, hm⟩ := hc
  simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hm
  have hud : p.userDeclared c k = none := by simp [Program.userDeclared, hs, hconv]
  have hcs : p.classSubobjects c = [] := by
    simp only [Program.classSubobjects, Program.subobjectsOf, hb, List.append_nil, List.filterMap_map]
    rw [List.filterMap_eq_nil_iff]
    intro m hmem
    simp [Function.comp, (hm m hmem).2]
  have hsubs : ∀ g : Ty → Bool, ((p.subobjectsOf c).any fun t => t.stripConst.isClass && g t) = false := by
    intro g
    apply List.any_eq_false.mpr
    intro t ht
    simp only [Program.subobjectsOf, hb, List.append_nil, List.mem_map] at ht
    obtain ⟨m, hmem, rfl⟩ := ht
    simp [(hm m hmem).2]
  have hmems : ∀ g : Member → Bool,
      ((p.membersOf c).any fun m => (m.init && m.throwingInit) || (m.ty.stripConst.isClass && g m)) = false := by
    intro g
    apply List.any_eq_false.mpr
    intro m hmem
    simp [(hm m hmem).1, (hm m hmem).2]
  unfold Program.throwing
  obtain ⟨n, hn⟩ : ∃ n, p.length = n + 1 := ⟨p.length - 1, by omega⟩
  rw [hn]
  cases k <;> simp [Program.throwingWithin, hud, hcs, hb, hsubs, hmems]

/-- A potentially-throwing destructor propagates: a class with a
potentially constructed subobject of class type whose destructor is
potentially throwing, and whose own destructor has no noexcept-specifier,
has a potentially-throwing destructor. Stated within fuel, as the
judgement is: the class's destructor is decided one step above its
subobjects'. -/
@[std theorem "except.spec#8"]
theorem nothrow_propagates (p : Program) (fuel : Nat) (c m : Ty) (hm : m ∈ p.classSubobjects c)
    (hud : p.userDeclared c .dtor = none ∨ ∃ d, p.userDeclared c .dtor = some d ∧ d.noexcept = none)
    (ht : p.throwingWithin fuel m .dtor = true) : p.throwingWithin (fuel + 1) c .dtor = true := by
  have himpl : ((p.classSubobjects c).any fun m => p.throwingWithin fuel m .dtor) = true :=
    List.any_eq_true.mpr ⟨m, hm, ht⟩
  rcases hud with hud | ⟨d, hud, hne⟩
  · simp [Program.throwingWithin, hud, himpl]
  · simp [Program.throwingWithin, hud, hne, himpl]

/-- `is_nothrow_destructible` is `is_destructible` for a class whose
destructors, its own and its subobjects', carry no `noexcept(false)`:
a destructor without a specifier has the implicit exception
specification, which is potentially throwing only through a subobject's,
so no destructor of such a program throws. -/
@[std theorem "except.spec#8" "concept.destructible#1"]
theorem nothrow_destructible_eq (p : Program) (t : Ty) (ht : t.concrete = true)
    (hno : ∀ c s, s ∈ p.specialDecls c → s.kind = .dtor → s.noexcept ≠ some false) :
    p.trait .isNothrowDestructible [t] = p.trait .isDestructible [t] := by
  have hthrow : ∀ fuel c, p.throwingWithin fuel c .dtor = false := by
    intro fuel
    induction fuel with
    | zero => intro c; rfl
    | succ n ih =>
      intro c
      have himpl : ((p.classSubobjects c).any fun m => p.throwingWithin n m .dtor) = false :=
        List.any_eq_false.mpr fun m _ => by simp [ih m]
      cases hud : p.userDeclared c .dtor with
      | none => simp [Program.throwingWithin, hud, himpl]
      | some d =>
        have hd : d ∈ p.specialDecls c ∧ d.kind = .dtor := by
          unfold Program.userDeclared at hud
          have hmem := List.mem_of_find?_eq_some hud
          have hk := List.find?_some hud
          simp only [beq_iff_eq] at hk
          refine ⟨?_, hk⟩
          rcases List.mem_append.mp hmem with h | h
          · exact h
          · exfalso
            obtain ⟨conv, -, hc⟩ := List.mem_filterMap.mp h
            rcases copyMoveForm_kind c conv d hc with h' | h' <;> rw [h'] at hk <;> cases hk
        cases hne : d.noexcept with
        | none => simp [Program.throwingWithin, hud, hne, himpl]
        | some b =>
          cases b with
          | true => simp [Program.throwingWithin, hud, hne]
          | false => exact absurd hne (hno c d hd.1 hd.2)
  have hth : p.throwing t.stripConst .dtor = false := hthrow _ _
  simp [Program.trait, Trait.structural, ht, Program.nothrowDestructible, hth]

/-- `is_constructible` of a class is overload resolution over its
constructors for direct-initialization, with the usable-candidate check:
the trait's answer is the initialization's. -/
@[std theorem "meta.unary.prop#9"]
theorem trait_is_resolution (p : Program) (c : Ty) (args : List Ty) (hc : c.stripConst.isClass = true)
    (hr : c.isRef = false) (habs : p.abstract c.stripConst = false)
    (hall : (c :: args).all Ty.concrete = true) :
    p.trait .isConstructible (c :: args) =
      .ok (Program.usable p.facts c.stripConst
        (Program.resolveCtor p.facts p .direct c.stripConst (args.map Program.declval))) := by
  have hv := Ty.isClass_not_void c hc
  have hf := Ty.isClass_not_function c hc
  simp [Program.trait, Trait.structural, hall, Program.constructible, hv, hf, hr, hc, habs]

/-- No object of an abstract class is created: `is_constructible` of an
abstract class is false for every argument list. -/
@[std theorem "basic.def#5" "class.abstract#2"]
theorem abstract_not_constructible (p : Program) (c : Ty) (args : List Ty)
    (hc : c.stripConst.isClass = true) (hr : c.isRef = false) (habs : p.abstract c.stripConst = true) :
    p.constructible c args = .ok false ∧
      ((c :: args).all Ty.concrete = true → p.trait .isConstructible (c :: args) = .ok false) := by
  have hv := Ty.isClass_not_void c hc
  have hf := Ty.isClass_not_function c hc
  refine ⟨by simp [Program.constructible, hv, hf, hr, hc, habs], fun hall => ?_⟩
  simp [Program.trait, Trait.structural, hall, Program.constructible, hv, hf, hr, hc, habs]

/-- No special member of a polymorphic class is trivial, so a polymorphic
class is neither trivially copyable nor standard-layout nor empty. -/
@[std theorem "class.default.ctor#3" "class.copy.ctor#12" "class.copy.assign#9" "class.dtor#8"
  "class.prop#1" "class.prop#2"]
theorem polymorphic_not_trivial (p : Program) (c : Ty) (h : p.polymorphic c = true) :
    (∀ k, p.trivial c k = false) ∧ p.triviallyCopyableClass c = false ∧
      p.standardLayoutClass c = false ∧ p.emptyClass c = false := by
  have ht : ∀ k, p.trivial c k = false := by
    intro k
    unfold Program.trivial
    cases p.length with
    | zero => rfl
    | succ n =>
      simp only [Program.trivialWithin]
      split <;> simp [h]
  refine ⟨ht, ?_, ?_, ?_⟩
  · simp [Program.triviallyCopyableClass, ht]
  · unfold Program.standardLayoutClass
    cases p.length with
    | zero => rfl
    | succ n => simp [Program.standardLayoutWithin, h]
  · unfold Program.emptyClass
    cases p.length with
    | zero => rfl
    | succ n => simp [Program.emptyWithin, h]

/-- `is_convertible` between two class types is the implicit conversion
sequence of phase 11: a user-defined sequence converts, the ambiguous
sequence and none do not, and a standard sequence, the argument's own
class or a base, converts when the constructor it selects is usable. -/
@[std theorem "meta.rel#6"]
theorem is_convertible_eq_ics (p : Program) (f t : Ty) (hf : f.referred.stripConst.isClass = true)
    (ht : t.referred.stripConst.isClass = true) (habs : t.isRef = false → p.abstract t.stripConst = false)
    (hall : [f, t].all Ty.concrete = true) :
    p.trait .isConvertible [f, t] =
      .ok (match p.ics .copy (Program.declval f) t with
        | some (.userDefined ..) => true
        | some (.standard _) => p.copyInitUsable (Program.declval f) t
        | _ => false) := by
  have hv := Ty.referred_isClass_not_void t ht
  have hfv := Ty.referred_isClass_not_void f hf
  have hfn := Ty.referred_isClass_not_function t ht
  have hsrc : (Program.declval f).ty.stripConst.isClass = true := by
    simpa [Program.declval] using hf
  have habs' : (!t.isRef && t.stripConst.isClass && p.abstract t.stripConst) = false := by
    cases hr : t.isRef with
    | true => rfl
    | false => simp [habs hr]
  simp only [Program.trait, Trait.structural, hall, Program.convertible, hv, hfv, hfn,
    Bool.false_eq_true, ↓reduceIte, hsrc, Bool.not_true, Bool.false_and, habs']
  cases h : p.ics .copy (Program.declval f) t with
  | none => rfl
  | some u => cases u <;> rfl

end Overload
