-- Overload/Syntax.lean                                               -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Std

/-!
# Syntax as data

Types, template arguments, and constant template argument values are
inductive types. The fragment is the one the typeclass encoding exercises:
named types, template parameters, `const`, pointer and reference
adjustments, class template specializations, constant template arguments,
and the non-deduced context marker.

A template parameter is referred to by its position in the template head,
so `Ty.param 0` is the first parameter of whichever head is in force.

`Ty` is one inductive type, with template argument lists spelled inside it
as `Ty.nil` and `Ty.cons` and a constant template argument as `Ty.value`.
A mutual or nested definition would read more naturally, and would make
every proof about deduction a proof by mutual induction. One type keeps
`induction` ordinary; `Ty.args` and `Ty.spec'` give the readable spelling.

Constant template arguments are structural values: trees with decidable
equality. That equality is the model's template-argument equivalence, and
`Val.Equivalent` transcribes [temp.type]/2 so the two can be compared
(`Val.equivalent_iff`).
-/

namespace Overload

/-- A template parameter, by position in the template head. -/
abbrev ParamIdx := Nat

/-- A constant template argument value. Class values are their direct
subobjects, in declaration order, which is what [temp.type]/2 compares;
the subobjects are a `nil`/`cons` chain for the reason `Ty`'s arguments
are. -/
inductive Val where
  /-- A value of integral type. -/
  | int : Int → Val
  /-- A value of type `bool`. -/
  | bool : Bool → Val
  /-- A value of class type, named, with its direct subobjects. -/
  | obj : String → Val → Val
  /-- The end of a subobject list. -/
  | nil : Val
  /-- A subobject followed by the rest. -/
  | cons : Val → Val → Val
  /-- A constant template parameter, by position. -/
  | param : ParamIdx → Val
  deriving Repr, DecidableEq, Inhabited

namespace Val

/-- A subobject list as a `Val` chain. -/
def list : List Val → Val
  | [] => .nil
  | v :: vs => .cons v (list vs)

/-- A class value, from its subobjects as a list. -/
def obj' (c : String) (vs : List Val) : Val := .obj c (list vs)

/-- The list form of a subobject chain, when it is one. -/
def toList : Val → Option (List Val)
  | .nil => some []
  | .cons v vs => (toList vs).map (v :: ·)
  | _ => none

end Val

/-- A type of the fragment, and the template arguments that occur in one. -/
inductive Ty where
  /-- A fundamental or class type, by name: `int`, `A`. -/
  | named : String → Ty
  /-- A type template parameter, by position. -/
  | param : ParamIdx → Ty
  /-- `const T`. -/
  | const : Ty → Ty
  /-- `T*`. -/
  | ptr : Ty → Ty
  /-- `T&`. -/
  | lref : Ty → Ty
  /-- `T&&`. -/
  | rref : Ty → Ty
  /-- A class template specialization `C<args>`; `args` is a `nil`/`cons`
  chain. -/
  | spec : String → Ty → Ty
  /-- The empty template argument list. -/
  | nil : Ty
  /-- A template argument followed by the rest of the list. -/
  | cons : Ty → Ty → Ty
  /-- A constant template argument. -/
  | value : Val → Ty
  /-- A non-deduced context around a type: deduction does not look inside,
  substitution does ([temp.deduct.type]/4). -/
  | nondeduced : Ty → Ty
  /-- The value of a variable template specialization `name<arg>`, such as
  `functor<T>`: a separately instantiated construct. Substituting into it
  instantiates it, which is outside the immediate context, and the
  environment's oracle says what comes of that. -/
  | lookup : String → Ty → Ty
  deriving Repr, DecidableEq, Inhabited

namespace Ty

/-- A template argument list as a `Ty` chain. -/
def args : List Ty → Ty
  | [] => .nil
  | a :: as => .cons a (args as)

/-- `C<args>`, from a list. -/
def spec' (c : String) (as : List Ty) : Ty := .spec c (args as)

/-- The list form of an argument chain, when it is one. -/
def toList : Ty → Option (List Ty)
  | .nil => some []
  | .cons a as => (toList as).map (a :: ·)
  | _ => none

/-- A type, as opposed to an argument list or a value: what a type template
parameter may be bound to. -/
def isType : Ty → Bool
  | .nil | .cons _ _ | .value _ | .lookup _ _ => false
  | _ => true

/-- Is `t` a reference type? -/
def isRef : Ty → Bool
  | .lref _ | .rref _ => true
  | _ => false

/-- Strip top-level `const`. -/
def stripConst : Ty → Ty
  | .const t => t
  | t => t

/-- The type a reference refers to; the type itself otherwise. -/
def referred : Ty → Ty
  | .lref t | .rref t => t
  | t => t

/-- Reference collapsing ([dcl.ref]/6): forming a reference to a reference
type yields an lvalue reference if either is one, else an rvalue
reference. -/
def collapse : Ty → Ty
  | .lref (.lref t) | .lref (.rref t) | .rref (.lref t) => .lref t
  | .rref (.rref t) => .rref t
  | t => t

end Ty

/-- The arguments deduced or specified so far: a parameter position maps to
at most one argument. -/
abbrev Bindings := List (ParamIdx × Ty)

namespace Bindings

/-- The argument bound to parameter `i`, if any. -/
def lookup (σ : Bindings) (i : ParamIdx) : Option Ty :=
  (σ.find? (·.1 = i)).map (·.2)

end Bindings

/-- Replace the constant template parameters of a value. -/
def Val.subst (σ : Bindings) : Val → Val
  | .int n => .int n
  | .bool b => .bool b
  | .obj c vs => .obj c (Val.subst σ vs)
  | .nil => .nil
  | .cons v vs => .cons (Val.subst σ v) (Val.subst σ vs)
  | .param i =>
    match σ.lookup i with
    | some (.value v) => v
    | _ => .param i

/-- Replace the template parameters of a type by their bound arguments,
collapsing references as they are formed. Parameters with no binding are
left in place. -/
def Ty.subst (σ : Bindings) : Ty → Ty
  | .named n => .named n
  | .param i =>
    match σ.lookup i with
    | some t => if t.isType then t else .param i
    | none => .param i
  | .const t => .const (Ty.subst σ t)
  | .ptr t => .ptr (Ty.subst σ t)
  | .lref t => Ty.collapse (.lref (Ty.subst σ t))
  | .rref t => Ty.collapse (.rref (Ty.subst σ t))
  | .spec c as => .spec c (Ty.subst σ as)
  | .nil => .nil
  | .cons a as => .cons (Ty.subst σ a) (Ty.subst σ as)
  | .value v => .value (Val.subst σ v)
  | .nondeduced t => .nondeduced (Ty.subst σ t)
  | .lookup n a => .lookup n (Ty.subst σ a)

/-- Does the value mention a constant template parameter? -/
def Val.dependent : Val → Bool
  | .int _ | .bool _ | .nil => false
  | .obj _ vs => Val.dependent vs
  | .cons v vs => Val.dependent v || Val.dependent vs
  | .param _ => true

/-- Does the type mention any template parameter? -/
def Ty.dependent : Ty → Bool
  | .named _ | .nil => false
  | .param _ => true
  | .const t | .ptr t | .lref t | .rref t | .nondeduced t | .lookup _ t => Ty.dependent t
  | .spec _ as => Ty.dependent as
  | .cons a as => Ty.dependent a || Ty.dependent as
  | .value v => Val.dependent v

/-! ## Template-argument equivalence -/

/-- Two values are template-argument-equivalent, transcribing [temp.type]/2
for the value forms the fragment has. The relation is defined so that its
agreement with `Val`'s equality is a theorem, `Val.equivalent_iff`. -/
@[specification]
inductive Val.Equivalent : Val → Val → Prop where
  /-- They are of integral type and their values are the same. -/
  | int (n : Int) : Val.Equivalent (.int n) (.int n)
  /-- `bool` is an integral type: their values are the same. -/
  | bool (b : Bool) : Val.Equivalent (.bool b) (.bool b)
  /-- They are of class type and their corresponding direct subobjects are
  template-argument-equivalent. "Of the same type" is the class name;
  "corresponding" is positional, so the subobject lists have one length. -/
  | obj (c : String) (vs ws : Val) :
      Val.Equivalent vs ws → Val.Equivalent (.obj c vs) (.obj c ws)
  /-- The end of two subobject lists of the same length. -/
  | nil : Val.Equivalent .nil .nil
  /-- Corresponding subobjects, positionally. -/
  | cons (v w vs ws : Val) :
      Val.Equivalent v w → Val.Equivalent vs ws → Val.Equivalent (.cons v vs) (.cons w ws)
  /-- A constant template parameter stands for the same value as itself. -/
  | param (i : ParamIdx) : Val.Equivalent (.param i) (.param i)

attribute [std rule "temp.type#2"] Val.Equivalent.int
attribute [std rule "temp.type#2"] Val.Equivalent.bool
attribute [std rule "temp.type#2"] Val.Equivalent.obj
attribute [std rule "temp.type#2"] Val.Equivalent.nil
attribute [std rule "temp.type#2"] Val.Equivalent.cons
attribute [std rule "temp.type#2"] Val.Equivalent.param

theorem Val.Equivalent.eq {v w : Val} (h : Val.Equivalent v w) : v = w := by
  induction h with
  | int _ | bool _ | nil | param _ => rfl
  | obj c vs ws _ ih => rw [ih]
  | cons v w vs ws _ _ ih₁ ih₂ => rw [ih₁, ih₂]

theorem Val.Equivalent.refl (v : Val) : Val.Equivalent v v := by
  induction v with
  | int n => exact .int n
  | bool b => exact .bool b
  | obj c vs ih => exact .obj c vs vs ih
  | nil => exact .nil
  | cons v vs ih₁ ih₂ => exact .cons v v vs vs ih₁ ih₂
  | param i => exact .param i

/-- The model's equality on values is template-argument equivalence: the
argument-identity suspect of the plan, stated once. -/
theorem Val.equivalent_iff (v w : Val) : Val.Equivalent v w ↔ v = w :=
  ⟨Val.Equivalent.eq, fun h => h ▸ Val.Equivalent.refl v⟩

end Overload
