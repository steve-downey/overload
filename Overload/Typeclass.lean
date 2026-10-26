-- Overload/Typeclass.lean                                            -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Typeclass.Encoding
import Overload.Typeclass.Routes
import Overload.Typeclass.Inheritance
import Overload.Typeclass.Units
import Overload.Typeclass.Members
import Overload.Typeclass.Lookup
import Overload.Typeclass.Arguments
import Overload.Typeclass.Conversion
import Overload.Typeclass.ValueNature
import Overload.Typeclass.Laws
import Overload.Typeclass.Derivation
import Overload.Typeclass.Emit

/-!
# The typeclass encoding

Everything under `Overload.Typeclass` is about the encoding of
[beman.transpose](https://github.com/bemanproject/typeclass), defined on
top of the Standard side of the model and proved about that definition.
Nothing on the Standard side imports it; `#check_layering` in
`Overload.lean` fails the build if that changes.

The encoding, as the model has it: an instance is a partial specialization
of a variable template whose primary is `std::false_type`, so instance
lookup is the Standard side's `Program.selectInstance`, with `coherence`
and `stability` already proved there. Each operation is an object whose
one `operator()` finds the instance through a trailing `const auto &`
constant template parameter defaulted to the lookup, and is constrained on
the call through it.

* `Overload.Typeclass.Encoding`: the operation object, the environment the
  encoding defines, and stability at the call surface.
* `Overload.Typeclass.Routes`: pinning, the by-value policy, and the plan's
  three routes as an alternative design.
* `Overload.Typeclass.Inheritance`: the leaks of inheritance between
  instance types, outside the fragment where `inheritance_erasure` holds,
  and why superclass coherence is a law and not an identity.
* `Overload.Typeclass.Units`: divergence between translation units, and
  stability per unit.
* `Overload.Typeclass.Conversion`: what a user-defined conversion between
  instance types would cost, and why the encoding has none.
* `Overload.Typeclass.ValueNature`: the value nature of an instance type,
  the callable-copying rule as constraint against Mandate, refinement by
  normalization, and the member probe.
* `Overload.Typeclass.Laws`: the typeclass laws as semantic requirements,
  and the superclass-coherence obligation as a theorem with its law as
  hypothesis.
* `Overload.Typeclass.Members`: the member call as a parameter, operation
  objects with several `operator()`s, and algorithms over an instance.
* `Overload.Typeclass.Emit`: the emitted differential cases of the encoding.
-/
