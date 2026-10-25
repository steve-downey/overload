-- Overload/Aggregate.lean                                            -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Special

/-!
# Aggregates and their initialization

Which classes are aggregates, by [dcl.init.aggr]/1 on their declarations;
their elements, bases then members ([dcl.init.aggr]/2), which
`Program.elements` already lists for the class value; aggregate
initialization from a braced list of argument types, with `{}` for the
elements the list leaves out and a reference element without an
initializer a failure ([dcl.init.aggr]/4, /6); value-initialization of a
non-aggregate by its default constructor for `T{}` ([dcl.init.list]/3);
the parenthesized aggregate initialization of [dcl.init.general]/15,
which `Program.constructible` reaches when no constructor is viable; and
the implicit-lifetime classes of [class.prop]/8.

Out of the fragment, by `decisions.md#aggregate-fragment`: arrays,
designated initializers, anonymous unions, brace elision, inherited
constructors, and narrowing in list-initialization, since the
initializers are types and narrowing is a property of a value.
-/

namespace Overload

namespace Program

/-- The protected direct bases a program declares for a class. -/
def protectedBasesOf (p : Program) : Ty → List Ty
  | .named n =>
    (p.findSome? fun
      | .class m _ ps _ => if m = n then some ps else none
      | _ => none).getD []
  | _ => []

/-- An aggregate class: no user-declared constructor, a converting
constructor included and inherited constructors out of the fragment; no
protected direct base, every member of the fragment being public; and
no virtual function, with no virtual bases in the fragment. -/
@[std rule "dcl.init.aggr#1"]
def aggregate (p : Program) (c : Ty) : Bool :=
  c.isClass && !p.userDeclaredCtor c && (p.protectedBasesOf c).isEmpty && !p.polymorphic c

/-- The elements of a class with whether each has a default member
initializer: a base has none. -/
@[std rule "dcl.init.aggr#2"]
def elementsWith (p : Program) (c : Ty) : List (Ty × Bool) :=
  (p.directBases c).map (·, false) ++ (p.membersOf c).map fun m => (m.ty, m.init)

/-- An element of type `t` is copy-initialized from an initializer of
type `a`: an implicit conversion sequence forms and is not ambiguous,
and a by-value class element's copy-initialization selects a usable
constructor. -/
@[std rule "dcl.init.aggr#4" "dcl.init.general#15"]
def elementInit (p : Program) (a : CallArg) (t : Ty) : Bool :=
  match p.ics .copy a t with
  | none | some .ambiguous => false
  | some _ => p.copyInitUsable a t

/-- Value-initialization of an element of type `t` is well-formed: a
reference is no object and cannot be; a scalar is zero-initialized; a
class is default-initialized by a usable default constructor. -/
@[std rule "dcl.init.general#8"]
def valueInit (p : Program) (t : Ty) : Bool :=
  if t.isRef then false
  else if !t.stripConst.isClass then true
  else usable p.facts t.stripConst (resolveCtor p.facts p .direct t.stripConst [])

/-- `T{inits...}` is well-formed for the class `c`, within `fuel` steps of
nesting. No object of an abstract class is created. For an aggregate,
the first `k` elements are explicitly initialized, each copy-initialized
from its initializer, and more initializers than elements is ill-formed;
each remaining element is initialized from its default member
initializer if it has one, otherwise copy-initialized from `{}` if it is
not a reference, which for a scalar is zero-initialization and for a
class is `T{}` again, and otherwise the program is ill-formed. For a
non-aggregate class, `T{}` is value-initialization and `T{inits...}`
considers its constructors, which must select a usable one. -/
@[std rule "dcl.init.aggr#4" "dcl.init.aggr#6" "dcl.init.list#3" "basic.def#5"]
def braceInitWithin (p : Program) : Nat → Ty → List CallArg → Bool
  | 0, _, _ => false
  | fuel + 1, c, inits =>
    if p.abstract c then false
    else if p.aggregate c then
      let elems := p.elementsWith c
      decide (inits.length ≤ elems.length) &&
      ((elems.zip inits).all fun ((t, _), a) => p.elementInit a t) &&
      ((elems.drop inits.length).all fun (t, init) =>
        init || (!t.isRef && (!t.stripConst.isClass || p.braceInitWithin fuel t.stripConst [])))
    else usable p.facts c (resolveCtor p.facts p .direct c inits)

/-- `T{inits...}` is well-formed for the class `c`. -/
def braceInit (p : Program) (c : Ty) (inits : List CallArg) : Bool := p.braceInitWithin p.length c inits

/-- Parenthesized aggregate initialization, `T(args...)` when no
constructor is viable: `c` is an aggregate, there are no more arguments
than elements, each element with an argument is copy-initialized from
it, and each remaining element is initialized from its default member
initializer if it has one and value-initialized otherwise. -/
@[std rule "dcl.init.general#15"]
def parenAggregateInit (p : Program) (c : Ty) (args : List CallArg) : Bool :=
  let elems := p.elementsWith c
  p.aggregate c && decide (args.length ≤ elems.length) &&
    ((elems.zip args).all fun ((t, _), a) => p.elementInit a t) &&
    ((elems.drop args.length).all fun (t, init) => init || p.valueInit t)

/-- An implicit-lifetime class: an aggregate whose destructor is not
user-provided, or a class with a trivial eligible constructor and a
trivial, non-deleted destructor. -/
@[std rule "class.prop#8"]
def implicitLifetimeClass (p : Program) (c : Ty) : Bool :=
  (p.aggregate c && !(p.userDeclared c .dtor).any (·.body == .userProvided)) ||
  ([SmfKind.defaultCtor, .copyCtor, .moveCtor].any (fun k => p.eligible c k && p.trivial c k) &&
    p.trivial c .dtor && !p.isDeleted c .dtor)

end Program

/-- A class is an aggregate exactly by its declarations: no user-declared
constructor, no protected base, no virtual function. -/
@[std theorem "dcl.init.aggr#1"]
theorem aggregate_iff_declarations (p : Program) (c : Ty) :
    p.aggregate c = true ↔
      c.isClass = true ∧ p.userDeclaredCtor c = false ∧ p.protectedBasesOf c = [] ∧
        p.polymorphic c = false := by
  simp [Program.aggregate, List.isEmpty_iff, and_assoc]

/-- The elements with their initializers list the same types as the
elements. -/
theorem elementsWith_fst (p : Program) (c : Ty) : (p.elementsWith c).map (·.1) = p.elements c := by
  simp only [Program.elementsWith, Program.elements, List.map_append, List.map_map]
  congr 1
  · exact List.map_id'' (fun _ => rfl) _

end Overload
