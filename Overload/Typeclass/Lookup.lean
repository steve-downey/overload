-- Overload/Typeclass/Lookup.lean                                     -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Members
import Overload.Typeclass.Encoding

/-!
# What lookup finds for the operation object

beman.transpose declares each operation as an object: `struct fmap_fn {
template <...> auto operator()(...) const; }; inline constexpr fmap_fn
fmap{};`. The model so far took `fmap` to be a function template, which
is what resolution sees once the candidates are known, and assumed that
nothing else is a candidate: the `hothers` hypothesis of `call_stability`,
"no other candidate consults the lookup", met because a variable cannot
be overloaded. With name lookup in the model that is a theorem.

* `opClass` is the object as declared: a class, an object of it, and the
  `operator()` template, which is `fmapObject` under another name in the
  class's scope (`operatorMember`).
* `object_design_candidates`: a call `fmap(f, x)` whose unqualified
  lookup binds `fmap` to the object resolves over the class's call
  operators and nothing else, whatever the argument types' namespaces
  declare ([basic.lookup.argdep]/1, [over.call.object]/1).
* `call_stability_object`: resolution over the object's one `operator()`
  moves exactly as `call_stability` says, with `hothers` discharged:
  there is no other candidate to consult the lookup.
* `unconstrained_member_hides_constrained`: the member call through an
  instance type whose own `fmap` is unconstrained never reaches the
  derivation base's constrained one ([class.member.lookup]/3), which is
  the library finding of the audit (steve-downey/typeclass#10).
-/

namespace Overload.Typeclass

open PartialOrdering

/-- The `operator()` of the operation object's class: `fmapObject` under
that name in the class's scope. -/
def operatorMember (tc : String) (cls : String := "fmap_fn") (scope : Scope := []) :
    FunctionTemplate :=
  (fmapObject tc).at "operator()" (scope ++ [.class cls])

/-- The operation object as declared: the class, the object, and the
call operator. -/
def opClass (tc : String) (cls : String := "fmap_fn") (scope : Scope := []) : Program :=
  [ .class cls [] [] scope, .object "fmap" cls scope, .functionTemplate (operatorMember tc cls scope) ]

/-! ## The candidates -/

/-- With `fmap` bound to the object by unqualified lookup and its class
having the call candidates `cs`, its call operators with their implicit
object parameter and its surrogates, a call `fmap(args)` resolves over
those, with the object as the first argument, whatever else the program
declares under the name `fmap`: argument-dependent lookup is suppressed
by the object, and no function named `fmap` anywhere is a candidate. -/
theorem object_design_candidates (p : Program) (pos : Nat) (s : Scope) (cls : String) (sc : Scope)
    (cs : List Decl) (args : List CallArg)
    (hobj : unqualifiedLookup p pos s "fmap" = [.object "fmap" cls sc])
    (hcls : (p.classScope? cls).isSome = true)
    (hops : p.objectCandidates pos cls = .selected cs) :
    p.callCandidates pos s "fmap" args = .selected (cs, impliedObject cls :: args) := by
  rw [object_call_candidates p pos s "fmap" cls sc args hobj hcls, hops]
  rfl

/-- The object as declared, alone: the candidates of `fmap(f, x)` from
the point after it are its one `operator()` with its implicit object
parameter, and the object leads the arguments, for any arguments. -/
theorem opClass_candidates (args : List CallArg) :
    (opClass "functor").callCandidates 3 [] "fmap" args =
      .selected ([(Decl.functionTemplate (operatorMember "functor")).withImplicitObject],
                 impliedObject "fmap_fn" :: args) := by
  refine object_design_candidates _ 3 [] "fmap_fn" []
    [(Decl.functionTemplate (operatorMember "functor")).withImplicitObject]
    args (by decide) (by decide) (by decide)

/-! ## Stability through the object -/

private theorem map_index_at (ft : FunctionTemplate) (n : String) (s : Scope) (r : Resolution Candidate) :
    (r.map (Candidate.at ft n s)).map (·.index) = r.map (·.index) := by
  cases r <;> simp [Resolution.map, Candidate.at, Function.comp_def, List.map_map]

private theorem map_illFormed_at (ft : FunctionTemplate) (n : String) (s : Scope)
    (r : Resolution Candidate) :
    (∃ e, r.map (Candidate.at ft n s) = .illFormed e) ↔ ∃ e, r = .illFormed e := by
  cases r <;> simp [Resolution.map]

/-- Stability of a call of the operation object, as declared. Declaring
an instance anywhere leaves the resolution of `fmap(f, x)` over the
object's `operator()` unchanged unless the instance matches the key,
and then the call selects the operator through the new instance or is
ill-formed by an ambiguous lookup. This is `call_stability` with its
`hothers` hypothesis discharged: the candidates are the one operator,
so no other candidate consults the lookup. -/
theorem call_stability_object (p₁ p₂ : Program) (tc : String) (h : Head) (pat : Ty) (r : Ranking Conv)
    (cls : String) (sc : Scope) (f x : CallArg)
    (hf : f.ty.isType = true) (hx : x.ty.isType = true)
    (hfF : f.ty.formed = true) (hxF : x.ty.formed = true)
    (hfr : f.ty.isRef = false) (hxr : x.ty.isRef = false) (hxd : x.ty.dependent = false)
    (hsoft : (p₁ ++ p₂).any (fun | .lookup c => c = tc | _ => false) = true)
    (hhard : (p₁ ++ p₂).any (fun | .lookupHard c => c = tc | _ => false) = false) :
    let p := p₁ ++ p₂
    let p' := p₁ ++ .instance tc h pat :: p₂
    let decls := [Decl.functionTemplate (operatorMember tc cls sc)]
    (resolve .text (encodingEnv p') r decls [f, x]).map (·.index) =
        (resolve .text (encodingEnv p) r decls [f, x]).map (·.index) ∨
      (PatternMatches h pat x.ty.stripConst ∧
        (p'.selectInstance tc x.ty.stripConst = .selected (p₁.instancesOf tc).length ∨
          ∃ e, resolve .text (encodingEnv p') r decls [f, x] = .illFormed e)) := by
  intro p p' decls
  have hdecls : decls = [Decl.functionTemplate ((fmapObject tc).at "operator()" (sc ++ [.class cls]))] := rfl
  rw [hdecls, resolve_at_single, resolve_at_single, map_index_at, map_index_at, map_illFormed_at]
  rcases call_stability p₁ p₂ tc h pat r [.functionTemplate (fmapObject tc)] f x hf hx hfF hxF hfr hxr hxd
      hsoft hhard (by simp) (fun ft hft hne => absurd (by simpa using hft) hne) with e | ⟨hm, e | e⟩
  · exact .inl (by rw [e])
  · exact .inr ⟨hm, .inl e⟩
  · exact .inr ⟨hm, .inr e⟩

/-! ## The hidden constrained member -/

/-- A derivation base with a constrained `fmap`, and an instance type
that derives from it and declares an unconstrained `fmap` of its own:
the shape the audit found in the library's Functor instances. -/
def hidingInstanceProgram : Program :=
  [ .class "derive_functor"
  , .functionTemplate { name := "fmap", head := [{ kind := .type }, { kind := .type }]
                        params := [.rref (.param 0), .rref (.param 1)]
                        constraint := some (.atomic "fmap_shape" [.param 1])
                        scope := [.class "derive_functor"] }
  , .class "opt_impl" [.named "derive_functor"]
  , .functionTemplate { name := "fmap", head := [{ kind := .type }, { kind := .type }]
                        params := [.rref (.param 0), .rref (.param 1)]
                        scope := [.class "opt_impl"] } ]

/-- The search for `fmap` in `opt_impl` finds its own unconstrained
`fmap` and nothing from the base: a probe of the member through the
instance resolves over the unconstrained one, and the base's constraint
is never consulted. -/
theorem unconstrained_member_hides_constrained :
    hidingInstanceProgram.memberSearch 4 "opt_impl" "fmap" =
      .selected [.functionTemplate { name := "fmap", head := [{ kind := .type }, { kind := .type }]
                                     params := [.rref (.param 0), .rref (.param 1)]
                                     scope := [.class "opt_impl"] }] ∧
      (hidingInstanceProgram.memberCallAt (Env.ofProgram hidingInstanceProgram [("fmap_shape", [.named "int"], false)])
        4 "opt_impl" "fmap" [{ ty := .named "Fn" }, { ty := .named "int" }]).map (·.index) = .selected 0 := by
  refine ⟨by decide, rfl⟩

end Overload.Typeclass
