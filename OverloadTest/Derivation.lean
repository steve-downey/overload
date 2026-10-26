-- OverloadTest/Derivation.lean                                     -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of the derivation base and the resolved operation object: the
value type of an instance, the type a member call's object has through a
lookup, the instantiated members of `derive_functor<Impl>`, and the calls
through them. -/

open Overload Overload.Typeclass

private def int : Ty := .named "int"
private def tp : TemplateParam := { kind := .type }
private def p : Program := deriveExample
private def env : Env := Env.full p
private def boxInt : Ty := .spec' "box" [int]
private def dfBox : Ty := .spec' "derive_functor" [.named "box_impl"]
private def dfList : Ty := .spec' "derive_functor" [.named "list_impl"]

-- The value type of the selected instance, with the pattern's argument substituted.
#guard p.instanceValueType? "functor" boxInt == some dfBox
#guard p.instanceValueType? "functor" (.spec' "list" [int]) == some dfList
#guard p.instanceValueType? "functor" int == none
-- An instance without a value type keeps the lookup's own name for it.
#guard Program.instanceValueType? [.lookup "t", .instance "t" [tp] (.spec' "box" [.param 0])] "t" boxInt == none
-- The class of a member call's object through the lookup's variable.
#guard p.lookupValueType env (.ref (.lookup "functor" boxInt)) == .ok dfBox
#guard p.lookupValueType env (.lookup "functor" boxInt) == .ok dfBox
#guard p.lookupValueType env dfBox == .ok dfBox
#guard (p.lookupValueType env (.ref (.lookup "functor" int))) == .ok (.named "std::false_type")
#guard Ty.withClass (.lref (.const (.typeOf (.param 2)))) dfBox == .lref (.const dfBox)
#guard Ty.withClass (.rref int) dfBox == .rref dfBox
-- The members of derive_functor<box_impl>: the implementation substituted, the own parameters renumbered.
#guard p.memberSearch p.length dfBox "fmap" ==
  .selected [.functionTemplate
    { name := "fmap", head := [tp, tp], params := [.rref (.param 0), .rref (.param 1)]
      constraint := some (.requires [.memberCall (.lref (.const (.named "box_impl"))) "fmap" [.param 0, .param 1]]
        [.named "box_impl", .param 0, .param 1])
      scope := [.class "derive_functor"] }]
#guard p.directBases dfBox == [.named "box_impl"]
-- The member call on the base is the implementation's.
#guard (p.memberCallAt env p.length dfBox "fmap" [{ ty := .named "Fn" }, { ty := boxInt }]).map (·.index) == .selected 0
#guard (p.memberCallAt env p.length dfBox "fmap" [{ ty := int }, { ty := boxInt }]).map (·.index) == .noMatch
#guard (p.memberCallAt env p.length dfList "fmap" [{ ty := int }, { ty := .spec' "list" [int] }]).map (·.index) == .selected 0
-- The resolved operation object.
#guard (p.callAt env p.length [] "fmap" [{ ty := .named "Fn" }, { ty := boxInt }]).map (·.index) == .selected 0
#guard (p.callAt env p.length [] "fmap" [{ ty := int }, { ty := boxInt }]).map (·.index) == .noMatch
#guard (p.callAt env p.length [] "fmap" [{ ty := .named "Fn" }, { ty := int }]).map (·.index) == .noMatch
-- A const lvalue container deduces `const box<int>&` and keys the lookup at `box<int>` still.
#guard (p.callAt env p.length [] "fmap" [{ ty := .named "Fn" }, { ty := .const boxInt, lvalue := true }]).map (·.index)
  == .selected 0
-- The requirement itself, one level down.
#guard p.requirementHolds env (.memberCall (.lref (.const (.typeOf (.ref (.lookup "functor" boxInt))))) "fmap"
  [.named "Fn", boxInt]) == .ok true
#guard p.requirementHolds env (.memberCall (.lref (.const (.typeOf (.ref (.lookup "functor" boxInt))))) "fmap"
  [int, boxInt]) == .ok false
