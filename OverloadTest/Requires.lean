-- OverloadTest/Requires.lean                                         -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of concept normalization and requires-expressions. -/

open Overload

private def tparam : TemplateParam := { kind := .type }
private def cA : Ty := .named "A"
private def cB : Ty := .named "B"

/-- `concept C1 = is_class<T>; concept C2 = C1<T> && is_empty<T>;` -/
private def refined : Program :=
  [ .class "A", .conceptDef "C1" 1 (.trait .isClass [.param 0])
  , .conceptDef "C2" 1 (.conj (.conceptId "C1" [.param 0]) (.trait .isEmpty [.param 0])) ]

#guard refined.normalize (.conceptId "C2" [.param 3]) ==
  .conj (.trait .isClass [.param 3]) (.trait .isEmpty [.param 3])
#guard refined.normalize (.conceptId "C1" [cA]) == .trait .isClass [cA]
#guard refined.normalize (.conceptId "Nope" [cA]) == .conceptId "Nope" [cA]
#guard Constraint.subsumes (refined.normalize (.conceptId "C2" [.param 0]))
  (refined.normalize (.conceptId "C1" [.param 0]))
#guard !Constraint.subsumes (refined.normalize (.conceptId "C1" [.param 0]))
  (refined.normalize (.conceptId "C2" [.param 0]))
-- Compared by name, the concept-ids do not subsume one another.
#guard !Constraint.subsumes (.conceptId "C2" [.param 0]) (.conceptId "C1" [.param 0])

-- An unexpanded concept-id is a hard error in the program's environment.
#guard Constraint.satisfied (Env.full refined).atomic [(0, cA)] (.conceptId "Nope" [.param 0]) ==
  .hard "the concept Nope is not declared"
#guard Constraint.satisfied (Env.full refined).atomic [(0, cA)] (refined.normalize (.conceptId "C2" [.param 0])) ==
  .ok true

/-- `void g(A);` and a member `get` of `A`. -/
private def calls : Program :=
  [ .class "A", .class "B", .function "g" [cA], .function "get" [] [.class "A"], .classTemplate "S" [tparam] ]
private def env : Env := Env.full calls
private def base : Env := Env.ofProgram calls

#guard calls.requirementHolds base (.simple "g" [cA]) == .ok true
#guard calls.requirementHolds base (.simple "g" [cB]) == .ok false
#guard calls.requirementHolds base (.simple "h" [cA]) == .ok false
#guard calls.requirementHolds base (.memberCall cA "get" []) == .ok true
#guard calls.requirementHolds base (.memberCall cB "get" []) == .ok false
#guard calls.requirementHolds base (.type (Ty.spec' "S" [cA])) == .ok true
#guard calls.requirementHolds base (.type (Ty.spec' "S" [cA, cB])) == .ok false
#guard calls.requirementHolds base (.type (Ty.spec' "R" [cA])) == .ok false
#guard calls.requirementHolds base (.type cA) == .ok true
#guard calls.requirementHolds base (.type (.named "int")) == .ok true
#guard calls.requirementHolds base (.type (.named "Zed")) == .ok false

-- Lexical order: the first failing requirement decides, and the
-- expression is never soft.
#guard calls.requirementsHold base [.simple "g" [cA], .type (Ty.spec' "S" [cA])] == .ok true
#guard calls.requirementsHold base [.simple "g" [cB], .type (Ty.spec' "R" [cA])] == .ok false
#guard calls.requirementsHold base [] == .ok true

-- Through a constraint: the full environment answers, the base does not.
#guard Constraint.satisfied env.atomic [(0, cA)] (.requires [.simple "g" [.param 0]] [.param 0]) == .ok true
#guard Constraint.satisfied env.atomic [(0, cB)] (.requires [.simple "g" [.param 0]] [.param 0]) == .ok false
#guard Constraint.satisfied base.atomic [(0, cA)] (.requires [.simple "g" [.param 0]] [.param 0]) == .ok false

/-! ## Compound and nested requirements -/

/-- `int g(A); A& h(A&); B k(A) noexcept; struct A { int get() const; };`
with the concepts `same_as`, `HasG = requires { g(declval<T>()); }` and
`Wraps = requires { requires HasG<T>; }`. -/
private def typed : Program :=
  [ .class "A", .class "B"
  , .function "g" [cA] [] .none none (.named "int")
  , .function "h" [.lref cA] [] .none none (.lref cA)
  , .function "k" [cA] [] .none (some true) cB
  , .function "get" [] [.class "A"] .none none (.named "int")
  , .conceptDef "same_as" 2 (.trait .isSame [.param 0, .param 1])
  , .conceptDef "HasG" 1 (.requires [.simple "g" [.param 0]] [.param 0])
  , .conceptDef "Wraps" 1 (.requires [.nested (.conceptId "HasG" [.param 0])] [.param 0]) ]
private def tenv : Env := Env.full typed
private def tbase : Env := Env.ofProgram typed

-- What an expression is: its type is the selected function's return
-- type, a reference included, and it throws unless the function says not.
#guard typed.expression tbase (.simple "g" [cA]) == .ok (some { ty := .named "int", throwing := some true })
#guard typed.expression tbase (.simple "h" [.lref cA]) == .ok (some { ty := .lref cA, throwing := some true })
#guard typed.expression tbase (.simple "k" [cA]) == .ok (some { ty := cB, throwing := some false })
#guard typed.expression tbase (.simple "g" [cB]) == .ok none
#guard typed.expression tbase (.memberCall cA "get" []) == .ok (some { ty := .named "int", throwing := some true })
#guard typed.expression tbase (.braceInit cA []) == .ok (some { ty := cA })
#guard typed.expression tbase (.type cA) == .soft "the requirement is not an expression"

-- Compound requirements: the return-type-requirement on `decltype((E))`.
#guard typed.requirementHolds tbase (.compound (.simple "g" [cA]) (some ("same_as", [.named "int"]))) == .ok true
#guard typed.requirementHolds tbase (.compound (.simple "g" [cA]) (some ("same_as", [cA]))) == .ok false
#guard typed.requirementHolds tbase (.compound (.simple "h" [.lref cA]) (some ("same_as", [.lref cA]))) == .ok true
#guard typed.requirementHolds tbase (.compound (.simple "h" [.lref cA]) (some ("same_as", [cA]))) == .ok false
#guard typed.requirementHolds tbase (.compound (.simple "g" [cB]) (some ("same_as", [.named "int"]))) == .ok false
#guard typed.requirementHolds tbase (.compound (.simple "g" [cA])) == .ok true
#guard typed.requirementHolds tbase (.compound (.simple "g" [cB])) == .ok false
#guard typed.requirementHolds tbase (.compound (.memberCall cA "get" []) (some ("same_as", [.named "int"]))) == .ok true
#guard typed.requirementHolds tbase (.compound (.braceInit cA []) (some ("same_as", [cA]))) == .ok true
#guard typed.requirementHolds tbase (.compound (.type cA) (some ("same_as", [cA]))) == .ok false

-- The noexcept-specifier.
#guard typed.requirementHolds tbase (.compound (.simple "k" [cA]) none true) == .ok true
#guard typed.requirementHolds tbase (.compound (.simple "g" [cA]) none true) == .ok false
#guard typed.requirementHolds tbase (.compound (.simple "k" [cA]) (some ("same_as", [cB])) true) == .ok true
#guard typed.requirementHolds tbase (.compound (.simple "k" [cA]) (some ("same_as", [cA])) true) == .ok false
-- Whether a braced initialization throws is outside the fragment: soft,
-- so the requires-expression is `false`.
#guard typed.requirementHolds tbase (.compound (.braceInit cA []) none true)
  == .soft "whether the expression throws is outside the fragment"
#guard typed.requirementsHold tbase [.compound (.braceInit cA []) none true] == .ok false

-- Nested requirements: satisfied in the environment, concept-ids expanded.
#guard typed.requirementHolds tbase (.nested (.conceptId "same_as" [cA, cA])) == .ok true
#guard typed.requirementHolds tbase (.nested (.conceptId "same_as" [cA, cB])) == .ok false
#guard typed.requirementHolds tbase (.nested (.trait .isClass [cA])) == .ok true
#guard typed.requirementHolds tbase (.nested (.conj (.trait .isClass [cA]) (.trait .isClass [.named "int"]))) == .ok false
#guard typed.requirementHolds tbase (.nested (.disj (.trait .isClass [cA]) (.trait .isClass [.named "int"]))) == .ok true
#guard typed.requirementHolds tbase (.nested (.conceptId "Nope" [cA])) == .hard "the concept Nope is not declared"

-- A nested concept whose body is a requires-expression: the base
-- environment answers it softly, the full one to the program's depth.
#guard typed.requirementHolds tbase (.nested (.conceptId "HasG" [cA])) == .ok false
#guard typed.requirementHolds tenv (.nested (.conceptId "HasG" [cA])) == .ok true
#guard typed.requirementHolds tenv (.nested (.conceptId "HasG" [cB])) == .ok false
#guard Constraint.satisfied tenv.atomic [(0, cA)] (typed.normalize (.conceptId "Wraps" [.param 0])) == .ok true
#guard Constraint.satisfied tenv.atomic [(0, cB)] (typed.normalize (.conceptId "Wraps" [.param 0])) == .ok false
#guard Constraint.satisfied (Env.fullWithin typed [] (fun e _ => .soft e) typed.trait 1).atomic [(0, cA)]
  (typed.normalize (.conceptId "Wraps" [.param 0])) == .ok false

-- The equivalence of the compound form with the simple and nested ones,
-- on the program.
#guard typed.requirementsHold tbase [.compound (.simple "g" [cA]) (some ("same_as", [.named "int"]))] ==
  typed.requirementsHold tbase [.simple "g" [cA], .nested (.conceptId "same_as" [.named "int", .named "int"])]
#guard typed.requirementsHold tbase [.compound (.simple "g" [cB]) (some ("same_as", [.named "int"]))] ==
  typed.requirementsHold tbase [.simple "g" [cB]]

-- Substitution reaches the new forms.
#guard (Constraint.Requirement.compound (.simple "g" [.param 0]) (some ("same_as", [.param 1]))).subst [(0, cA), (1, cB)]
  == .compound (.simple "g" [cA]) (some ("same_as", [cB]))
#guard (Constraint.Requirement.nested (.conj (.conceptId "C" [.param 0]) (.trait .isClass [.param 0]))).subst [(0, cA)]
  == .nested (.conj (.conceptId "C" [cA]) (.trait .isClass [cA]))

/-! ## A class callee -/

private def cF : Ty := .named "F"
/-- `struct F { int operator()(int) const noexcept; }`, `struct G` whose
`operator()` is a template constrained on `is_invocable_v<F, T>`,
`struct H {}`, and `struct D : F {}`. -/
private def callable : Program :=
  [ .class "A", .class "F"
  , .function "operator()" [.named "int"] [.class "F"] .none (some true) (.named "int")
  , .class "G"
  , .functionTemplate { name := "operator()", head := [tparam], params := [.param 0], ret := cA
                        scope := [.class "G"], constraint := some (.trait .isInvocable [cF, .param 0]) }
  , .class "H", .class "D" [cF] ]
private def cenv : Env := Env.full callable
private def cbase : Env := Env.ofProgram callable
private def cone : Env := Env.fullWithin callable [] (fun e _ => .soft e) callable.trait 1

-- The base environment leaves a class callee to the residue; the one
-- above answers it by the call on the object.
#guard cbase.atomic (.trait .isInvocable) [cF, .named "int"]
  == .soft "is_invocable of a class callee is resolved above the environment"
#guard cone.atomic (.trait .isInvocable) [cF, .named "int"] == .ok true
#guard cenv.atomic (.trait .isInvocable) [cF, .named "int"] == .ok true
#guard cenv.atomic (.trait .isInvocable) [.lref (.const cF), .named "int"] == .ok true
#guard cenv.atomic (.trait .isInvocable) [.rref cF, .named "int"] == .ok true
#guard cenv.atomic (.trait .isInvocable) [cF, cA] == .ok false
#guard cenv.atomic (.trait .isInvocable) [cF, .named "int", .named "int"] == .ok false
#guard cenv.atomic (.trait .isInvocable) [cF] == .ok false
#guard cenv.atomic (.trait .isInvocable) [.named "H", .named "int"] == .ok false
#guard cenv.atomic (.trait .isInvocable) [.named "D", .named "int"] == .ok true
-- A callee that is not a class is what the base answers.
#guard cenv.atomic (.trait .isInvocable) [.named "int", .named "int"] == .ok false
#guard cenv.atomic (.trait .isInvocable) [Ty.fn' [.named "int"] cA, .named "int"] == .ok true

-- The call's expression: the return type and whether it throws.
#guard callable.objectInvoke cbase (Program.declval cF) "F" [.named "int"] == .ok (some { ty := .named "int", throwing := some false })
#guard callable.objectInvoke cbase (Program.declval (.named "H")) "H" [.named "int"] == .ok none
#guard callable.objectInvoke cone (Program.declval (.named "G")) "G" [.named "int"] == .ok (some { ty := cA, throwing := some true })

-- Depth: `G`'s call operator is constrained on `is_invocable_v<F, T>`,
-- which the environment below must answer, so one level is not enough.
#guard cone.atomic (.trait .isInvocable) [.named "G", .named "int"] == .ok false
#guard cenv.atomic (.trait .isInvocable) [.named "G", .named "int"] == .ok true
#guard cenv.atomic (.trait .isInvocable) [.named "G", cA] == .ok false

-- Known not to throw.
#guard cenv.atomic (.trait .isNothrowInvocable) [cF, .named "int"] == .ok true
#guard cenv.atomic (.trait .isNothrowInvocable) [.named "G", .named "int"] == .ok false
#guard cenv.atomic (.trait .isNothrowInvocable) [.named "H", .named "int"] == .ok false
#guard cbase.atomic (.trait .isNothrowInvocable) [cF, .named "int"]
  == .soft "is_invocable of a class callee is resolved above the environment"

-- The trait is the call on the object, on the program.
#guard (callable.traitAbove cbase .isInvocable [cF, .named "int"] == .ok true)
  == (callable.objectCallAt cbase callable.length "F" (Program.declval cF) [Program.declval (.named "int")]
        matches .selected _)
#guard (callable.traitAbove cone .isInvocable [.named "G", cA] == .ok true)
  == (callable.objectCallAt cone callable.length "G" (Program.declval (.named "G")) [Program.declval cA]
        matches .selected _)

/-! ## Surrogate call functions -/

private def fp : Ty := .ptr (.fn' [.named "int"] (.named "int"))
private def fpNoexcept : Ty := .ptr (.fn' [.named "int"] (.named "int") true)
/-- `S` converts to `int(*)(int)` through a `const` conversion function,
`N` through a non-const one, `R` to `int(&)(int)`, `T` to a `noexcept`
pointer through a `noexcept` conversion, `U` to a `noexcept` pointer
through a conversion that may throw, `O` has a call operator beside its
conversion, and `W` two conversions to the same pointer. -/
private def surrogates : Program :=
  [ .class "S", .converting (.named "S") (.function fp)
  , .class "N", .converting (.named "N") (.function fp false false)
  , .class "R", .converting (.named "R") (.function (.lref (.fn' [.named "int"] (.named "int"))))
  , .class "T", .converting (.named "T") (.function fpNoexcept false true (some true))
  , .class "U", .converting (.named "U") (.function fpNoexcept)
  , .class "O", .function "operator()" [.named "int"] [.class "O"] .none none cA
  , .converting (.named "O") (.function fp)
  , .class "W", .converting (.named "W") (.function fp), .converting (.named "W") (.function (.lref fp))
  , .class "X", .converting (.named "X") (.function fp true) ]
private def senv : Env := Env.full surrogates

#guard surrogates.surrogates "S" == [.function "call-function" [fp, .named "int"] [] .none none (.named "int")]
#guard surrogates.surrogates "T" == [.function "call-function" [fpNoexcept, .named "int"] [] .none (some true) (.named "int")]
#guard surrogates.surrogates "U" == [.function "call-function" [fpNoexcept, .named "int"] [] .none none (.named "int")]
-- An explicit conversion function gives no surrogate.
#guard surrogates.surrogates "X" == []
#guard surrogates.objectCandidates surrogates.length "X" == .illFormed "X has no function call operator"

#guard senv.atomic (.trait .isInvocable) [.named "S", .named "int"] == .ok true
#guard senv.atomic (.trait .isInvocable) [.lref (.const (.named "S")), .named "int"] == .ok true
#guard senv.atomic (.trait .isInvocable) [.named "S"] == .ok false
#guard senv.atomic (.trait .isInvocable) [.named "S", cA] == .ok false
-- A non-const conversion function: not on a const object, yes on an rvalue.
#guard senv.atomic (.trait .isInvocable) [.lref (.const (.named "N")), .named "int"] == .ok false
#guard senv.atomic (.trait .isInvocable) [.named "N", .named "int"] == .ok true
#guard senv.atomic (.trait .isInvocable) [.lref (.named "N"), .named "int"] == .ok true
#guard senv.atomic (.trait .isInvocable) [.named "R", .named "int"] == .ok true
#guard senv.atomic (.trait .isInvocable) [.named "X", .named "int"] == .ok false
-- Known not to throw: both the conversion and the function.
#guard senv.atomic (.trait .isNothrowInvocable) [.named "T", .named "int"] == .ok true
#guard senv.atomic (.trait .isNothrowInvocable) [.named "U", .named "int"] == .ok false
#guard senv.atomic (.trait .isNothrowInvocable) [.named "S", .named "int"] == .ok false
-- The call operator beats the surrogate; two surrogates are ambiguous.
#guard (surrogates.objectCallAt senv surrogates.length "O" (Program.declval (.named "O"))
  [Program.declval (.named "int")]).map (·.index) == .selected 0
#guard surrogates.objectInvoke senv (Program.declval (.named "O")) "O" [.named "int"] == .ok (some { ty := cA, throwing := some true })
#guard (surrogates.objectCallAt senv surrogates.length "W" (Program.declval (.named "W"))
  [Program.declval (.named "int")]) matches .ambiguous _
#guard senv.atomic (.trait .isInvocable) [.named "W", .named "int"] == .ok false
