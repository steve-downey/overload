-- OverloadTest/Names.lean                                            -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-! Tests of name lookup: single and unqualified search over scopes, what
lookup found, and a call from a point. -/

open Overload

private def int : Ty := .named "int"
private def char : Ty := .named "char"
private def user : Scope := [.namespace "user"]
private def a : Scope := [.namespace "a"]
private def ab : Scope := [.namespace "a", .namespace "b"]

/-- `void f(int); struct X {}; namespace user { void f(char); }
namespace a::b { inline constexpr pinned_instance obj{}; void f(int); }` -/
private def p : Program :=
  [ .function "f" [int], .class "X", .function "f" [char] user
  , .object "obj" "pinned_instance" ab, .function "f" [int] ab ]

-- A single search sees one scope, and only the declarations before the point.
#guard singleSearch p 5 [] "f" == [.function "f" [int]]
#guard singleSearch p 0 [] "f" == []
#guard singleSearch p 5 user "f" == [.function "f" [char] user]
#guard singleSearch p 5 ab "f" == [.function "f" [int] ab]
#guard singleSearch p 4 ab "f" == []

-- An unqualified search stops at the first enclosing scope that binds the name.
#guard unqualifiedSearch p 5 ab "f" == [.function "f" [int] ab]
#guard unqualifiedSearch p 5 a "f" == [.function "f" [int]]
#guard unqualifiedSearch p 5 user "f" == [.function "f" [char] user]
#guard unqualifiedSearch p 5 user "g" == []
#guard unqualifiedSearch p 2 user "f" == [.function "f" [int]]
#guard unqualifiedSearch p 5 ab "obj" == [.object "obj" "pinned_instance" ab]
#guard unqualifiedSearch p 5 user "X" == [.class "X"]

-- What lookup found.
#guard lookupResult [] == .none
#guard lookupResult [.function "f" [int], .function "f" [int]] == .overloadSet [.function "f" [int]]
#guard lookupResult [.function "f" [int], .function "f" [char]] ==
  .overloadSet [.function "f" [int], .function "f" [char]]
-- A class is discarded when anything else is found ([basic.lookup.general]/4).
#guard lookupResult [.class "f", .function "f" [int]] == .overloadSet [.function "f" [int]]
#guard lookupResult [.class "f"] == .entity (.class "f")
#guard lookupResult [.object "f", .object "f"] == .entity (.object "f")
#guard lookupResult [.object "f", .function "f" [int]] == .ambiguous [.object "f", .function "f" [int]]

-- A call from a point: lookup, then resolution over the overload set.
#guard (p.callAt (Env.ofProgram p) 5 ab "f" [{ ty := int }]).map (·.index) == .selected 0
-- The ranking has no integral conversion, so the hidden exact match leaves the call not viable.
#guard (p.callAt (Env.ofProgram p) 5 user "f" [{ ty := int }]).map (·.index) == .noMatch
#guard (p.callAt (Env.ofProgram p) 5 user "f" [{ ty := char }]).map (·.index) == .selected 0
#guard (p.callAt (Env.ofProgram p) 5 [] "f" [{ ty := int }]).map (·.index) == .selected 0
#guard (p.callAt (Env.ofProgram p) 5 ab "obj" [{ ty := int }]) matches .illFormed _
#guard (p.callAt (Env.ofProgram p) 5 [] "h" [{ ty := int }]) matches .illFormed _
#guard (p.callAt (Env.ofProgram p) 0 [] "f" [{ ty := int }]) matches .illFormed _

-- The scope field is seen: a namespaced function is a candidate and an entity.
#guard Program.candidates [.function "f" [int] user] "f" == [.function "f" [int] user]
#guard (Decl.function "f" [int] user).scope == user
#guard (Decl.function "f" [int]).scope == []
#guard !sameEntity (.function "f" [int]) (.function "f" [int] user)
#guard corresponds (.function "f" [int]) (.function "f" [int] user)
#guard entities [.function "f" [int], .function "f" [int] user] ==
  [.function "f" [int], .function "f" [int] user]
