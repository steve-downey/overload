-- Overload/Separability.lean                                         -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Typeclass

/-!
# Separability: what the conversion ranking cannot reach

The plan's separability theorem: the instance selected is invariant under
the choice of conversion ranking. The model makes it a statement about
any two rankings, of any conversion types. If both select a candidate at
the same position, they select the same candidate, specialization and
all (`separability`). A specialization's template arguments are where an
instance enters a function's identity, so the ranking chooses among
candidates and never changes what a candidate is.

One lemma per suspect of the plan:

* step-order: a hard error in generating the candidates is the outcome
  under every ranking (`separability_step_order`);
* argument-identity: the selected specialization is the one deduction
  produced for its template, so its identity is fixed before any
  conversion is ranked (`separability_argument_identity`);
* argument-conversion: candidate generation, where template arguments are
  converted, does not consult the ranking, and every selected candidate
  is a generated one (`separability_argument_conversion`);
* tie-break-reach: when two candidates have the same conversion
  sequences, the ranking drops out and only the non-template preference
  and partial ordering decide (`separability_tie_break_reach`);
* rank-precedence: a worse conversion for any argument loses, whatever the
  non-template preference or partial ordering say
  (`separability_rank_precedence`), and the ranking is live: the program
  ranking and the identity ranking select differently on one call
  (`ranking_live`).
-/

namespace Overload

/-! ## Candidates carry distinct positions -/

/-- Indices at least `i`, strictly increasing. -/
private def Sorted (i : Nat) (cs : List Candidate) : Prop :=
  (∀ c ∈ cs, i ≤ c.index) ∧ cs.Pairwise (fun a b => a.index < b.index)

private theorem sorted_cons {i : Nat} {c : Candidate} {rest : List Candidate}
    (hc : c.index = i) (h : Sorted (i + 1) rest) : Sorted i (c :: rest) := by
  obtain ⟨hlow, hpw⟩ := h
  refine ⟨?_, List.pairwise_cons.mpr ⟨fun c' hc' => by have := hlow c' hc'; omega, hpw⟩⟩
  intro c' hc'
  rcases List.mem_cons.mp hc' with rfl | hc'
  · omega
  · have := hlow c' hc'; omega

private theorem sorted_skip {i : Nat} {cs : List Candidate} (h : Sorted (i + 1) cs) :
    Sorted i cs :=
  ⟨fun c hc => by have := h.1 c hc; omega, h.2⟩

theorem generate_go_sorted (env : Env) (args : List CallArg) (explicit : List Ty) (s : Bool) :
    ∀ (ds : List Decl) (i : Nat) (cs : List Candidate),
      generate.go env args explicit ds i s = .ok cs →
        (∀ c ∈ cs, i ≤ c.index) ∧ cs.Pairwise (fun a b => a.index < b.index) := by
  intro ds
  induction ds with
  | nil => intro i cs h; cases h; simp
  | cons d ds ih =>
    intro i cs h
    show Sorted i cs
    cases d with
    | function n ps =>
      cases hg : generate.go env args explicit ds (i + 1) s with
      | ok rest =>
        simp only [generate.go, hg, Subst.bind_eq, Subst.bind_ok, Subst.pure_eq, Subst.ok.injEq] at h
        subst h
        exact sorted_cons rfl (ih _ _ hg)
      | soft r => simp [generate.go, hg] at h
      | hard r => simp [generate.go, hg] at h
    | functionTemplate ft =>
      cases s with
      | true =>
        simp only [generate.go, ↓reduceIte] at h
        exact sorted_skip (ih _ _ h)
      | false =>
        simp only [generate.go, Bool.false_eq_true, ↓reduceIte] at h
        cases hd : deduceTemplate env ft explicit args with
        | ok sp =>
          rw [hd] at h
          cases hg : generate.go env args explicit ds (i + 1) false with
          | ok rest =>
            simp only [hg, Subst.bind_eq, Subst.bind_ok, Subst.pure_eq, Subst.ok.injEq] at h
            subst h
            exact sorted_cons rfl (ih _ _ hg)
          | soft r => simp [hg] at h
          | hard r => simp [hg] at h
        | soft r => rw [hd] at h; exact sorted_skip (ih _ _ h)
        | hard r => rw [hd] at h; cases h
    | _ => simp only [generate.go] at h; exact sorted_skip (ih _ _ h)

/-- A generated template candidate's specialization is what deduction
produced for one of the declarations. -/
theorem generate_go_deduced (env : Env) (args : List CallArg) (explicit : List Ty) (s : Bool) :
    ∀ (ds : List Decl) (i : Nat) (cs : List Candidate),
      generate.go env args explicit ds i s = .ok cs →
        ∀ c ∈ cs, ∀ sp, c.specialization = some sp →
          ∃ ft, .functionTemplate ft ∈ ds ∧ deduceTemplate env ft explicit args = .ok sp := by
  intro ds
  induction ds with
  | nil => intro i cs h; cases h; simp
  | cons d ds ih =>
    intro i cs h c hc sp hsp
    have later : ∀ cs', generate.go env args explicit ds (i + 1) s = .ok cs' → c ∈ cs' →
        ∃ ft, .functionTemplate ft ∈ d :: ds ∧ deduceTemplate env ft explicit args = .ok sp := by
      intro cs' hg hc'
      obtain ⟨ft, hm, hd⟩ := ih (i + 1) cs' hg c hc' sp hsp
      exact ⟨ft, List.mem_cons_of_mem _ hm, hd⟩
    cases d with
    | function n ps =>
      cases hg : generate.go env args explicit ds (i + 1) s with
      | ok rest =>
        simp only [generate.go, hg, Subst.bind_eq, Subst.bind_ok, Subst.pure_eq, Subst.ok.injEq] at h
        subst h
        rcases List.mem_cons.mp hc with rfl | hc
        · cases hsp
        · exact later rest hg hc
      | soft r => simp [generate.go, hg] at h
      | hard r => simp [generate.go, hg] at h
    | functionTemplate ft =>
      cases s with
      | true =>
        simp only [generate.go, ↓reduceIte] at h
        exact later cs h hc
      | false =>
        simp only [generate.go, Bool.false_eq_true, ↓reduceIte] at h
        cases hd : deduceTemplate env ft explicit args with
        | ok sp' =>
          rw [hd] at h
          cases hg : generate.go env args explicit ds (i + 1) false with
          | ok rest =>
            simp only [hg, Subst.bind_eq, Subst.bind_ok, Subst.pure_eq, Subst.ok.injEq] at h
            subst h
            rcases List.mem_cons.mp hc with rfl | hc
            · cases hsp
              exact ⟨ft, List.mem_cons_self, hd⟩
            · exact later rest hg hc
          | soft r => simp [hg] at h
          | hard r => simp [hg] at h
        | soft r => rw [hd] at h; exact later cs h hc
        | hard r => rw [hd] at h; cases h
    | _ => simp only [generate.go] at h; exact later cs h hc

/-! ## Viable functions and the best are drawn from the candidates -/

theorem viable_go_sublist (r : Ranking Conv) (args : List CallArg) :
    ∀ (cs : List Candidate) (vs : List (Viable Conv)),
      viable.go r args cs = .ok vs → (vs.map (·.cand)).Sublist cs := by
  intro cs
  induction cs with
  | nil => intro vs h; cases h; simp
  | cons c cs ih =>
    intro vs h
    simp only [viable.go] at h
    split at h
    · cases hc : conversions r args c.params with
      | ok o =>
        rw [hc] at h
        cases o with
        | some convs =>
          cases hg : viable.go r args cs with
          | ok rest =>
            simp only [Subst.bind_eq, Subst.bind_ok, hg, Subst.pure_eq, Subst.ok.injEq] at h
            subst h
            simpa using ih rest hg
          | soft _ => simp [hg] at h
          | hard _ => simp [hg] at h
        | none =>
          simp only [Subst.bind_eq, Subst.bind_ok] at h
          exact (ih vs h).cons c
      | soft _ => rw [hc] at h; cases h
      | hard _ => rw [hc] at h; cases h
    · exact (ih vs h).cons c

theorem bestViable_mem (r : Ranking Conv) (ms : Specialization → Specialization → Bool)
    (vs : List (Viable Conv)) (c : Candidate) (h : bestViable r ms vs = .selected c) :
    c ∈ vs.map (·.cand) := by
  unfold bestViable at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · rename_i w hw
      cases h
      have : w ∈ List.filter (fun w => vs.all fun f => f.cand.index == w.cand.index || betterFunction r ms w f) vs := by
        rw [hw]; exact List.mem_singleton_self w
      exact List.mem_map.mpr ⟨w, (List.mem_filter.mp this).1, rfl⟩
    · cases h
    · cases h

/-- Whatever the ranking, a selected candidate is one that candidate
generation produced. -/
theorem resolve_selected_mem (mode : Mode) (env : Env) (r : Ranking Conv) (decls : List Decl)
    (args : List CallArg) (explicit : List Ty) (c : Candidate)
    (h : resolve mode env r decls args explicit = .selected c) :
    ∃ cs, generate mode env decls args explicit = .ok cs ∧ c ∈ cs := by
  unfold resolve at h
  split at h
  · cases h
  · cases h
  · rename_i cs hcs
    split at h
    · cases h
    · cases h
    · rename_i vs hvs
      have hsub : (vs.map (·.cand)).Sublist cs := viable_go_sublist r args cs vs hvs
      exact ⟨cs, hcs, hsub.subset (bestViable_mem r _ vs c h)⟩

private theorem pairwise_index_eq {cs : List Candidate}
    (hpw : cs.Pairwise (fun a b => a.index < b.index)) :
    ∀ a ∈ cs, ∀ b ∈ cs, a.index = b.index → a = b := by
  induction cs with
  | nil => intro a ha; cases ha
  | cons c cs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpw
    intro a ha b hb hab
    rcases List.mem_cons.mp ha with ha | ha <;> rcases List.mem_cons.mp hb with hb | hb
    · rw [ha, hb]
    · have := hhead b hb; rw [ha] at hab; omega
    · have := hhead a ha; rw [hb] at hab; omega
    · exact ih htail a ha b hb hab

/-! ## The separability theorem -/

/-- Separability: two rankings, of any conversion types, that both select
a candidate at the same position select the same candidate, with the same
specialization and so the same template arguments, instances included.
The ranking chooses among candidates; it never changes one. -/
theorem separability (mode : Mode) (env : Env) (r₁ : Ranking C₁) (r₂ : Ranking C₂)
    (decls : List Decl) (args : List CallArg) (explicit : List Ty) (c₁ c₂ : Candidate)
    (h₁ : resolve mode env r₁ decls args explicit = .selected c₁)
    (h₂ : resolve mode env r₂ decls args explicit = .selected c₂)
    (hi : c₁.index = c₂.index) : c₁ = c₂ := by
  obtain ⟨cs, hcs, hm₁⟩ := resolve_selected_mem mode env r₁ decls args explicit c₁ h₁
  obtain ⟨cs', hcs', hm₂⟩ := resolve_selected_mem mode env r₂ decls args explicit c₂ h₂
  rw [hcs] at hcs'
  cases hcs'
  exact pairwise_index_eq (generate_go_sorted env args explicit _ decls 0 cs hcs).2 c₁ hm₁ c₂ hm₂ hi

/-- The step-order suspect: a hard error while generating the candidates,
such as a lookup failing outside the immediate context in a default
template argument, is the outcome under every ranking. No ranking rescues
the call. -/
theorem separability_step_order (mode : Mode) (env : Env) (decls : List Decl)
    (args : List CallArg) (explicit : List Ty) (e : Reason)
    (h : generate mode env decls args explicit = .hard e) (r : Ranking Conv) :
    resolve mode env r decls args explicit = .illFormed e := by
  simp [resolve, h]

/-- The argument-identity suspect: the specialization of a selected
template candidate, whose template arguments are where an instance
enters the function's identity, is what deduction produced for its
template. Deduction does not consult the ranking. -/
theorem separability_argument_identity (mode : Mode) (env : Env) (r : Ranking Conv)
    (decls : List Decl) (args : List CallArg) (explicit : List Ty) (c : Candidate)
    (sp : Specialization) (h : resolve mode env r decls args explicit = .selected c)
    (hsp : c.specialization = some sp) :
    ∃ ft, .functionTemplate ft ∈ decls ∧ deduceTemplate env ft explicit args = .ok sp := by
  obtain ⟨cs, hcs, hm⟩ := resolve_selected_mem mode env r decls args explicit c h
  exact generate_go_deduced env args explicit _ decls 0 cs hcs c hm sp hsp

/-- The argument-conversion suspect: conversions of template arguments
belong to deduction, inside candidate generation, which takes no ranking.
Every ranking selects from the one candidate list. -/
theorem separability_argument_conversion (mode : Mode) (env : Env) (r : Ranking Conv)
    (decls : List Decl) (args : List CallArg) (explicit : List Ty) (c : Candidate)
    (h : resolve mode env r decls args explicit = .selected c) :
    ∃ cs, generate mode env decls args explicit = .ok cs ∧ c ∈ cs :=
  resolve_selected_mem mode env r decls args explicit c h

private theorem zip_self_all (r : Ranking Conv) (hirr : ∀ c, r.better c c = false) (l : List Conv) :
    ((l.zip l).all fun (c₁, c₂) => !r.better c₂ c₁) = true ∧
      ((l.zip l).any fun (c₁, c₂) => r.better c₁ c₂) = false := by
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons c l ih => simp [List.zip_cons_cons, hirr, ih.1, ih.2]

/-- The tie-break-reach suspect: when two viable functions have the same
conversion sequences, an irreflexive ranking drops out, and the
non-template preference and partial ordering, with the gate of
[temp.func.order]/8 inside it, are all that decide. -/
theorem separability_tie_break_reach (r : Ranking Conv) (hirr : ∀ c, r.better c c = false)
    (ms : Specialization → Specialization → Bool) (f₁ f₂ : Viable Conv)
    (h : f₁.convs = f₂.convs) :
    betterFunction r ms f₁ f₂ =
      ((!f₁.cand.isTemplate && f₂.cand.isTemplate) ||
        match f₁.cand.specialization, f₂.cand.specialization with
        | some s₁, some s₂ => ms s₁ s₂
        | _, _ => false) := by
  obtain ⟨hall, hany⟩ := zip_self_all r hirr f₂.convs
  simp only [betterFunction, h, hall, hany, Bool.true_and, Bool.false_or]
  rfl

/-- The rank-precedence suspect: a viable function with a worse conversion
sequence for some argument is not a better function, whatever the
non-template preference and partial ordering say. Conversions are
compared first ([over.match.best.general]/2). -/
theorem separability_rank_precedence (r : Ranking Conv)
    (ms : Specialization → Specialization → Bool) (f₁ f₂ : Viable Conv)
    (h : ∃ p ∈ f₁.convs.zip f₂.convs, r.better p.2 p.1 = true) :
    betterFunction r ms f₁ f₂ = false := by
  obtain ⟨⟨c₁, c₂⟩, hm, hb⟩ := h
  have : ((f₁.convs.zip f₂.convs).all fun (c₁, c₂) => !r.better c₂ c₁) = false := by
    rw [List.all_eq_false]
    exact ⟨(c₁, c₂), hm, by simpa using hb⟩
  simp only [betterFunction, this, Bool.false_and]

/-! ## The ranking is live -/

/-- Three classes in a chain and two functions taking the lower two by
value, the draft's example of [over.ics.rank]/4 without the pointers. -/
def derivedChain : Program :=
  [ .class "A", .class "B" ["A"], .class "C" ["B"]
  , .function "f" [.named "A"], .function "f" [.named "B"] ]

/-- The ranking is live: on one call the program's ranking selects
`f(B)`, by the derived-to-base rule, and the identity ranking finds no
viable function. Separability bounds what a ranking reaches; it does not
make the ranking irrelevant. -/
theorem ranking_live :
    (resolve .text (Env.ofProgram derivedChain) derivedChain.ranking
        (derivedChain.candidates "f") [{ ty := .named "C" }]).map (·.index) = .selected 1 ∧
      (resolve .text (Env.ofProgram derivedChain) identityRanking
        (derivedChain.candidates "f") [{ ty := .named "C" }]).map (·.index) = .noMatch := by
  constructor <;> rfl

/-! ## Inheritance leak 1: rank beats the preference for a refinement -/

/-- An Applicative instance type derived from a Functor one, a Monad
instance type derived from that, a generic `use(const T&)` and one that
names the Applicative instance type concretely. -/
def rankLeak : Program :=
  [ .class "functor_i", .class "applicative_i" ["functor_i"], .class "monad_i" ["applicative_i"]
  , .functionTemplate { name := "use", head := [{ kind := .type }], params := [.lref (.const (.param 0))] }
  , .function "use" [.lref (.const (.named "applicative_i"))] ]

/-- Leak 1 of the plan's instance inheritance: at the Applicative instance
type, the non-template overload naming it wins the tie; at the Monad
instance type derived from it, the generic template wins, because an
exact match beats a derived-to-base conversion before the non-template
preference is consulted. Deriving one instance type from another moves
the call to the less refined overload. -/
theorem rank_beats_refinement :
    (resolve .text (Env.ofProgram rankLeak) rankLeak.ranking (rankLeak.candidates "use")
        [{ ty := .named "applicative_i", lvalue := true }]).map (·.index) = .selected 1 ∧
      (resolve .text (Env.ofProgram rankLeak) rankLeak.ranking (rankLeak.candidates "use")
        [{ ty := .named "monad_i", lvalue := true }]).map (·.index) = .selected 0 := by
  constructor <;> rfl

end Overload
