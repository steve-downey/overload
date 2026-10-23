-- Overload/Environment.lean                                          -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Lookup
import Overload.Ranking

/-!
# The environment a program defines

`Env` is the oracle of the `expression-depth` decision: what the model
does not model, the environment answers. A program defines one.

* Instantiating a variable template specialization `tc<a>` is lookup over
  the program's partial specializations. A selected specialization has a
  value, which the model names by the type `instance_of<a, i>`. An
  ambiguous lookup is a hard error, since matching partial specializations
  is part of instantiation and so outside the immediate context
  ([temp.deduct.general]/8). A primary either has a value of its own, the
  soft design, or a `static_assert` that fires, the hard design.
* The atomic constraints the model knows about a lookup, `has_instance`
  and `lookup_formed`, are answered from the same selection. Any other
  atomic constraint is answered from the case's table, and failing that by
  `extra`, which a layer above the Standard can supply for constraints
  whose meaning is its own.
* Convertibility is the existence of an implicit conversion sequence under
  the program's ranking (`Program.ics`), and the bases are the program's.
-/

namespace Overload

/-- The environment a program defines. `atomics` is the case's table of
ground truths for the concepts it declares; `extra` answers any atomic
constraint neither the lookup rules nor the table know. -/
def Env.ofProgram (p : Program) (atomics : List (String × List Ty × Bool) := [])
    (extra : Constraint.Oracle := fun e _ => .soft s!"unknown atomic constraint {e}") : Env :=
  { instantiate := fun n a =>
      let hard := p.any fun | .lookupHard c => c = n | _ => false
      let soft := p.any fun | .lookup c => c = n | _ => false
      match p.selectInstance n a with
      | .selected i => .ok (.spec' "instance_of" [a, .value (.int i)])
      | .ambiguous _ => .hard s!"ambiguous partial specializations of {n}<{repr a}>"
      | .illFormed r => .hard r
      | .noMatch =>
        if hard then .hard s!"static_assert in the primary {n}<{repr a}>"
        else if soft then .ok (.named "std::false_type")
        else .soft s!"no variable template {n}"
    atomic := fun e args =>
      match e, args with
      -- The lookup selects a partial specialization rather than the primary.
      | "has_instance", [.named c, a] => .ok ((p.selectInstance c a).toOption.isSome)
      -- A condition that names a lookup's variable, `sizeof(decltype(
      -- tc<a>)) > 0`: true when the variable can be instantiated, and a
      -- failure outside the immediate context when it cannot.
      | "lookup_formed", [.named c, a] =>
        match p.selectInstance c a with
        | .selected _ => .ok true
        | .ambiguous _ => .hard s!"ambiguous partial specializations of {c}<{repr a}>"
        | .illFormed r => .hard r
        | .noMatch =>
          if p.any fun | .lookupHard c' => c' = c | _ => false then
            .hard s!"static_assert in the primary {c}<{repr a}>"
          else .ok true
      | _, _ =>
        match atomics.find? fun (e', args', _) => e' == e && args' == args with
        | some (_, _, b) => .ok b
        | none => extra e args
    convertible := fun a t => .ok (p.ics .copy a t).isSome
    bases := p.allBases
    subobject := p.subobject }

/-- What instantiating a lookup gives in a program whose primary is the
soft design: the selected specialization's value, the primary's, or a
hard error for an ambiguous lookup. -/
theorem Env.ofProgram_instantiate (p : Program) (atomics : List (String × List Ty × Bool))
    (extra : Constraint.Oracle) (tc : String) (a : Ty)
    (hsoft : p.any (fun | .lookup c => c = tc | _ => false) = true)
    (hhard : p.any (fun | .lookupHard c => c = tc | _ => false) = false) :
    (Env.ofProgram p atomics extra).instantiate tc a =
      match p.selectInstance tc a with
      | .selected i => .ok (.spec' "instance_of" [a, .value (.int i)])
      | .ambiguous _ => .hard s!"ambiguous partial specializations of {tc}<{repr a}>"
      | .illFormed r => .hard r
      | .noMatch => .ok (.named "std::false_type") := by
  simp only [Env.ofProgram, hsoft, hhard]
  split <;> simp

end Overload
