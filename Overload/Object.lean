-- Overload/Object.lean                                               -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Object.Storage
import Overload.Object.Syntax
import Overload.Object.Model
import Overload.Object.State
import Overload.Object.Machine
import Overload.Object.Access
import Overload.Object.Launder
import Overload.Object.Profile
import Overload.Object.P4222
import Overload.Object.P4416
import Overload.Object.Functions
import Overload.Object.Emit

/-!
# The object model

Storage, objects, lifetime, initialization and destruction, as an
abstract machine over the Standard side's classes: `Overload.Object.*`.
It is on the Standard side, imports the type system for triviality,
aggregates and implicit-lifetime classes, and says nothing about the
typeclass encoding. `docs/guide.md` has the map and `docs/plan.md`
phase 16 the charter.
-/
