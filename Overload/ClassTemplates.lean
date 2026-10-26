-- Overload/ClassTemplates.lean                                       -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Members
import Overload.Requires

/-!
# Class templates and their members

A class template's members are declarations for its current
instantiation, `X<T0, …>` (`currentInstantiation`), and its member
functions are declarations in its scope, which is a class scope. A
specialization has the template's member declarations with its
arguments substituted (`Decl.instantiate`), which is the implicit
instantiation of their declarations that looking into the
specialization requires ([temp.inst]/2, /3); the argument list is
determined by the type ([temp.mem.func]/2, `Program.classKey?`). A
member template's own parameters follow the class's in the numbering
([temp.mem]/1), and the same substitution renumbers them from zero.

* `instantiate_ground`: a class's member is the declaration itself;
  there is nothing to substitute.
* `member_template_arguments_example`: for a member template of a class
  template specialization, deduction binds the member's own parameters
  only, and gives the function type that deduction for the member with
  the class's arguments as leading explicit arguments gives
  ([temp.mem.func]/2). Shown by computation on `holder<int>`; the
  general statement is owed (`docs/plan.md`, phase 15).
* `specialization_members_fixed`: the point of instantiation of a
  specialization referenced from a non-template context precedes the
  first declaration that refers to it ([temp.point]/4,
  `Program.pointOfInstantiation`); in a program whose class templates'
  members all precede that point (`Program.templatesWellFormed`), the
  declaration set of the specialization is the same from every point at
  or after it, which is what one point of instantiation per unit
  ([temp.point]/7) comes to for a model without definitions.
* `specialization_callee_invocable`: `is_invocable` of a class template
  specialization callee is computed as the call on the object, through
  a call operator or a surrogate of the specialization; the residue of
  `decisions.md#trait-residue` is closed.
* `argument_reference_deletes`: a class template with a member of its
  parameter's type has its copy assignment deleted at a reference
  argument and not at an object type ([class.copy.assign]/7): value
  nature is a property of the specialization, decided by the argument.
-/

namespace Overload

/-- A class's member is its declaration: with no template arguments
there is nothing to substitute. -/
theorem instantiate_ground (d : Decl) : Decl.instantiate [] d = d := by
  simp [Decl.instantiate]

/-- The class template's key is its own name with no arguments. -/
theorem classKey?_named (p : Program) (n : String) : p.classKey? (.named n) = some (.named n, []) := rfl

/-- `template <class T> struct holder { T m; template <class U> void f(T, U) const; };`,
with the member template's own parameter numbered after the class's. -/
def holderProgram : Program :=
  [ .classTemplate "holder" [{ kind := .type }]
  , .member (currentInstantiation "holder" [{ kind := .type }]) { name := "m", ty := .param 0 }
  , .functionTemplate holderMember ]
where
  /-- The member template as declared in the class template: `T` is
  `.param 0`, the class's; `U` is `.param 1`, its own. -/
  holderMember : FunctionTemplate :=
    { name := "f", head := [{ kind := .type }], params := [.param 0, .param 1]
      scope := [.class "holder"] }

/-- The member template of `holder<int>`: `template <class U> void f(int, U)`. -/
theorem holder_int_member :
    Decl.instantiate [.named "int"] (.functionTemplate holderProgram.holderMember) =
      .functionTemplate { name := "f", head := [{ kind := .type }], params := [.named "int", .param 0]
                          scope := [.class "holder"] } := by
  decide

/-- The data member of `holder<int>` is `int m`. -/
theorem holder_int_data :
    holderProgram.membersOf (.spec' "holder" [.named "int"]) = [{ name := "m", ty := .named "int" }] := by
  decide

/-- The member template with the class's head prepended, as an out-of-line
definition writes it: `template <class T> template <class U> void
holder<T>::f(T, U)`. -/
def holderProgram.combined : FunctionTemplate :=
  { holderProgram.holderMember with head := [{ kind := .type }, { kind := .type }] }

/-- Deduction for the instantiated member of `holder<int>` at `(int, char)`
binds `U` alone and gives the function type `(int, char)`; deduction for
the combined template with `int` as the leading explicit argument gives
the same function type, with `T` bound as well. -/
@[std example "temp.mem.func#2"]
theorem member_template_arguments_example :
    let env := Env.ofProgram holderProgram
    let args : List CallArg := [{ ty := .named "int" }, { ty := .named "char" }]
    (deduceTemplate env { holderProgram.holderMember with params := [.named "int", .param 0] } [] args).map
        (fun s => (s.args, s.params)) =
      .ok ([(0, .named "char")], [.named "int", .named "char"]) ∧
    (deduceTemplate env holderProgram.combined [.named "int"] args).map (fun s => (s.args, s.params)) =
      .ok ([(1, .named "char"), (0, .named "int")], [.named "int", .named "char"]) := by
  constructor <;> rfl

/-! ## Where a specialization is instantiated -/

/-- Does a type, or a part of one, satisfy a predicate? -/
def Ty.has (f : Ty → Bool) : Ty → Bool
  | .named n => f (.named n)
  | .param i => f (.param i)
  | .const t => f (.const t) || Ty.has f t
  | .ptr t => f (.ptr t) || Ty.has f t
  | .lref t => f (.lref t) || Ty.has f t
  | .rref t => f (.rref t) || Ty.has f t
  | .spec c as => f (.spec c as) || Ty.has f as
  | .nil => f .nil
  | .cons a as => f (.cons a as) || (Ty.has f a || Ty.has f as)
  | .value v => f (.value v)
  | .nondeduced t => f (.nondeduced t) || Ty.has f t
  | .lookup n a => f (.lookup n a) || Ty.has f a
  | .ref t => f (.ref t) || Ty.has f t
  | .removeCvref t => f (.removeCvref t) || Ty.has f t
  | .typeOf t => f (.typeOf t) || Ty.has f t
  | .enableIf c as t => f (.enableIf c as t) || (Ty.has f as || Ty.has f t)
  | .fn ps r ne => f (.fn ps r ne) || (Ty.has f ps || Ty.has f r)
  | .synth i => f (.synth i)

theorem Ty.has_mono {f g : Ty → Bool} (hfg : ∀ t, f t = true → g t = true) (u : Ty)
    (h : Ty.has f u = true) : Ty.has g u = true := by
  induction u <;> simp only [Ty.has, Bool.or_eq_true] at h ⊢ <;>
    first
    | exact hfg _ h
    | (rcases h with h | h
       · exact Or.inl (hfg _ h)
       · exact Or.inr (by simp_all))
    | (rcases h with h | h | h
       · exact Or.inl (hfg _ h)
       · exact Or.inr (Or.inl (by simp_all))
       · exact Or.inr (Or.inr (by simp_all)))

/-- The types a declaration mentions: its bases, parameters, return type,
defaults, pattern, member types and class. -/
def Decl.types : Decl → List Ty
  | .class _ bs ps _ => bs ++ ps
  | .classTemplate _ h bs ps _ => h.filterMap (·.default) ++ bs ++ ps
  | .function _ ps _ _ _ r => ps ++ [r]
  | .functionTemplate ft => ft.head.filterMap (·.default) ++ ft.params ++ [ft.ret]
  | .instance _ h pat v => h.filterMap (·.default) ++ pat :: v.toList
  | .use _ t => [t]
  | .object _ cls _ => [.named cls]
  | .dependentCall _ args _ => args.map (·.ty)
  | .converting c conv => c :: (match conv with | .constructor t .. => [t] | .function t .. => [t])
  | .member c m => [c, m.ty]
  | .special c _ => [c]
  | .lookup _ | .lookupHard _ | .concept .. | .conceptDef .. | .semantic .. | .refersTo _ => []

/-- Does a declaration refer to a type, as it or as a part of one it
mentions? -/
def Decl.mentions (t : Ty) (d : Decl) : Bool := d.types.any (Ty.has (· == t))

/-- Does a declaration refer to a specialization of a class template with
ground arguments? A dependent one, the current instantiation among them,
is a reference from a templated context, which is not a point of
instantiation of its own. -/
def Decl.mentionsSpecOf (n : String) (d : Decl) : Bool :=
  d.types.any (Ty.has fun | .spec m as => m == n && !as.dependent | _ => false)

theorem Decl.mentionsSpecOf_of_mentions (n : String) (as : Ty) (d : Decl) (hdep : as.dependent = false)
    (h : d.mentions (.spec n as) = true) : d.mentionsSpecOf n = true := by
  simp only [Decl.mentions, Decl.mentionsSpecOf, List.any_eq_true] at h ⊢
  obtain ⟨t, ht, hhas⟩ := h
  refine ⟨t, ht, Ty.has_mono (fun u hu => ?_) t hhas⟩
  rw [beq_iff_eq] at hu
  subst hu
  simp [hdep]

/-- The class type a member, special member or conversion is declared
for. -/
def Decl.memberKey? : Decl → Option Ty
  | .member c _ | .special c _ | .converting c _ => some c
  | _ => none

/-- The point of instantiation of a class template specialization
referenced from a non-template context: it immediately precedes the
namespace-scope declaration that refers to it, so the position of the
first declaration that mentions the type; `none` when nothing does. -/
@[std rule "temp.point#4"]
def Program.pointOfInstantiation (p : Program) (c : Ty) : Option Nat :=
  p.zipIdx.findSome? fun (d, i) => if d.mentions c then some i else none

/-- The positions of a class template's members: the declarations in its
scope, and those declared for its current instantiation. -/
def Program.templateMembers (p : Program) (n : String) (sc : Scope) (h : Head) : List Nat :=
  p.zipIdx.filterMap fun (d, j) =>
    if d.scope == sc ++ [.class n] || d.memberKey? == some (currentInstantiation n h) then some j else none

/-- Every member of a class template follows the template's declaration
and precedes every declaration that refers to a ground specialization of
it: the specialization's members are complete at its point of
instantiation. A property of the program's shape, like
`scopesWellFormed`. -/
@[std rule "temp.inst#3" "temp.point#4"]
def Program.templatesWellFormed (p : Program) : Bool :=
  p.zipIdx.all fun (d, i) =>
    match d with
    | .classTemplate n h _ _ sc =>
      (p.templateMembers n sc h).all (fun j => i < j) &&
        p.zipIdx.all fun (e, k) => !e.mentionsSpecOf n || (p.templateMembers n sc h).all (· < k)
    | _ => true

/-- A specialization's key is the current instantiation of its declared
template. -/
theorem classKey?_spec (p : Program) (n : String) (as : Ty) (k : Ty) (args : List Ty)
    (hk : p.classKey? (.spec n as) = some (k, args)) :
    ∃ h bs ps, p.classTemplateDecl? n = some (h, bs, ps) ∧ k = currentInstantiation n h := by
  simp only [Program.classKey?] at hk
  split at hk
  · rename_i h bs ps l hdecl hl
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hk
    obtain ⟨args', -, hkey, -⟩ := hk
    exact ⟨h, bs, ps, hdecl, hkey.symm⟩
  · simp at hk

/-- A filter over a prefix is stable once nothing from `q` on passes it. -/
theorem filter_take_stable {α} (f : α → Bool) : ∀ (l : List α) (q pos : Nat), q ≤ pos →
    (∀ k, q ≤ k → ∀ x, l[k]? = some x → f x = false) →
    (l.take pos).filter f = (l.take q).filter f := by
  intro l
  induction l with
  | nil => intros; simp
  | cons a l ih =>
    intro q pos hqp h
    cases q with
    | zero =>
      simp only [List.take_zero, List.filter_nil]
      apply List.filter_eq_nil_iff.2
      intro x hx
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 (List.mem_of_mem_take hx)
      simp [h i (Nat.zero_le _) x hi]
    | succ q =>
      cases pos with
      | zero => omega
      | succ pos =>
        simp only [List.take_succ_cons, List.filter_cons]
        have := ih q pos (by omega) (fun k hk x hx => h (k + 1) (by omega) x (by simpa using hx))
        split <;> simp [this]

/-- The declaration set of a class template specialization is the same
from every point at or after its point of instantiation, in a program
whose class templates' members precede every reference to a
specialization: a specialization has one point of instantiation in a
unit, and its members are what the template had declared by then. -/
@[std theorem "temp.point#7.sentence-2" "temp.inst#3"]
theorem specialization_members_fixed (p : Program) (n : String) (as : Ty) (name : String) (q pos : Nat)
    (hdep : as.dependent = false) (hwf : p.templatesWellFormed = true)
    (hq : p.pointOfInstantiation (.spec n as) = some q) (hpos : q ≤ pos) :
    p.declarationSet pos (.spec n as) name = p.declarationSet q (.spec n as) name := by
  unfold Program.declarationSet
  cases hs : p.memberScope? (.spec n as) with
  | none => rfl
  | some s =>
    cases hk : p.classKey? (.spec n as) with
    | none => rfl
    | some ka =>
      simp only
      congr 1
      -- The scope is the template's, extended by its step.
      have hsc : ∃ sc h bs ps, (Decl.classTemplate n h bs ps sc) ∈ p ∧ s = sc ++ [.class n] := by
        obtain ⟨h, bs, ps, hdecl, hkey⟩ := classKey?_spec p n as ka.1 ka.2 hk
        simp only [Program.memberScope?, hk, Option.map_some, hkey, currentInstantiation, Ty.spec',
          Option.map_eq_some_iff] at hs
        obtain ⟨sc, hsc, rfl⟩ := hs
        obtain ⟨d, hd, hds⟩ := List.exists_of_findSome?_eq_some hsc
        cases d <;> try (simp at hds; done)
        rename_i m h' bs' ps' s'
        simp only at hds
        split at hds
        · rename_i hm
          simp only [Option.some.injEq] at hds
          subst hm hds
          exact ⟨_, _, _, _, hd, rfl⟩
        · simp at hds
      obtain ⟨sc, h, bs, ps, hmem, rfl⟩ := hsc
      -- The declaration at the point mentions the specialization.
      obtain ⟨⟨dq, iq⟩, hdq, hiq⟩ := List.exists_of_findSome?_eq_some hq
      simp only at hiq
      split at hiq
      · rename_i hment
        simp only [Option.some.injEq] at hiq
        subst hiq
        -- Well-formedness at the template's declaration.
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hmem
        have hwf' := List.all_eq_true.1 hwf (.classTemplate n h bs ps sc, i)
          (List.mem_zipIdx_iff_getElem?.2 hi)
        simp only [Bool.and_eq_true, List.all_eq_true] at hwf'
        have hbefore := hwf'.2 (dq, iq) hdq
        simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
          Decl.mentionsSpecOf_of_mentions n as dq hdep hment, Bool.false_eq_true, false_or,
          List.all_eq_true] at hbefore
        unfold singleSearch
        apply filter_take_stable _ p iq pos hpos
        intro k hk e he
        cases hb : e.binds (sc ++ [.class n]) name
        · simp [hb]
        · exfalso
          have hscope : e.scope = sc ++ [.class n] := by
            simp only [Decl.binds, Bool.and_eq_true, beq_iff_eq] at hb
            exact hb.2
          have hkmem : k ∈ p.templateMembers n sc h := by
            simp only [Program.templateMembers, List.mem_filterMap]
            refine ⟨(e, k), List.mem_zipIdx_iff_getElem?.2 he, ?_⟩
            simp [hscope]
          have := hbefore k hkmem
          simp only [decide_eq_true_eq] at this
          omega
      · simp at hiq

/-! ## The residue closed, and value nature by argument -/

/-- `struct A {}; template <class T> struct fn { T operator()(T) const; };`
and `template <class T> struct conv { operator int(*)(T)() const; };`. -/
def specializationCallee : Program :=
  [ .class "A", .classTemplate "fn" [{ kind := .type }]
  , .function "operator()" [.param 0] [.class "fn"] .none none (.param 0)
  , .classTemplate "conv" [{ kind := .type }]
  , .converting (currentInstantiation "conv" [{ kind := .type }])
      (.function (.ptr (.fn' [.param 0] (.named "int")))) ]

/-- `is_invocable` of a class template specialization callee is computed:
`fn<int>` on an `int`, `fn<A>` on an `A`, and `conv<int>` on an `int`
through its surrogate; `fn<int>` on an `A` is not. -/
@[std theorem "func.require#1" "meta.rel#3"]
theorem specialization_callee_invocable :
    let env := Env.full specializationCallee
    env.atomic (.trait .isInvocable) [.spec' "fn" [.named "int"], .named "int"] = .ok true ∧
    env.atomic (.trait .isInvocable) [.spec' "fn" [.named "A"], .named "A"] = .ok true ∧
    env.atomic (.trait .isInvocable) [.spec' "fn" [.named "int"], .named "A"] = .ok false ∧
    env.atomic (.trait .isInvocable) [.spec' "conv" [.named "int"], .named "int"] = .ok true := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- `template <class T> struct cell { T m; };`. -/
def cellProgram : Program :=
  [ .classTemplate "cell" [{ kind := .type }]
  , .member (currentInstantiation "cell" [{ kind := .type }]) { name := "m", ty := .param 0 } ]

/-- `cell<int&>` has its copy assignment deleted and is not of value
nature; `cell<int>` has every special member and is. The template is
one; the argument decides. -/
@[std theorem "class.copy.assign#7" "class.default.ctor#2"]
theorem argument_reference_deletes :
    cellProgram.deleted (.spec' "cell" [.lref (.named "int")]) .copyAssign = true ∧
    cellProgram.deleted (.spec' "cell" [.named "int"]) .copyAssign = false ∧
    cellProgram.valueNature (.spec' "cell" [.named "int"]) = true ∧
    cellProgram.valueNature (.spec' "cell" [.lref (.named "int")]) = false := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end Overload
