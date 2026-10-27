/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_eq_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 130
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Sym2
open scoped Cardinal
variable {α : Type*}
variable (α) in
open scoped Classical in
variable (α) in
variable (α) in
variable (α) in
open scoped Classical in
variable (α) in
variable (α) in
section fromRel
variable {r : α → α → Prop} (sym : Std.Symm r)

theorem cardinalMk_prod_eq_two_mul_cardinalMk_fromRel [Std.Irrefl r] :
    #{ p : α × α // r p.fst p.snd } = 2 * #(fromRel sym) := by
  classical
  let P := {p : α × α // r p.fst p.snd}
  have rep : ∀ e : fromRel sym, ∃ p : P, s(p.1.1, p.1.2) = e.1 := by
    rintro ⟨e, he⟩
    revert he
    refine Sym2.inductionOn e ?_
    intro a b hab
    exact ⟨⟨(a, b), by simpa using hab⟩, rfl⟩
  choose p hp using rep
  have hne (e : fromRel sym) : (p e).1.1 ≠ (p e).1.2 := by
    intro h
    have hr := (p e).property
    rw [h] at hr
    exact irrefl _ hr
  let f : Bool × fromRel sym → P := fun x =>
    if x.1 then
      ⟨((p x.2).1.2, (p x.2).1.1), sym.symm _ _ (p x.2).property⟩
    else p x.2
  have hf_edge (b : Bool) (e : fromRel sym) :
      s((f (b, e)).1.1, (f (b, e)).1.2) = e.1 := by
    cases b
    · exact hp e
    · change s((p e).1.2, (p e).1.1) = e.1
      calc
        s((p e).1.2, (p e).1.1) = s((p e).1.1, (p e).1.2) := by
          rw [Sym2.eq_iff]
          exact Or.inr ⟨rfl, rfl⟩
        _ = e.1 := hp e
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨b, e⟩ ⟨c, d⟩ h
      have hed : e = d := by
        apply Subtype.ext
        calc
          e.1 = s((f (b, e)).1.1, (f (b, e)).1.2) :=
            (hf_edge b e).symm
          _ = s((f (c, d)).1.1, (f (c, d)).1.2) :=
            congrArg (fun q : P => s(q.1.1, q.1.2)) h
          _ = d.1 := hf_edge c d
      subst d
      cases b <;> cases c
      · rfl
      · exact False.elim (hne e (congrArg (fun q : P => q.1.1) h))
      · exact False.elim (hne e (congrArg (fun q : P => q.1.1) h).symm)
      · rfl
    · intro q
      let e : fromRel sym :=
        ⟨s(q.1.1, q.1.2), by simpa using q.property⟩
      have he : s((p e).1.1, (p e).1.2) = s(q.1.1, q.1.2) := hp e
      have he' :
          ((p e).1.1 = q.1.1 ∧ (p e).1.2 = q.1.2) ∨
          ((p e).1.1 = q.1.2 ∧ (p e).1.2 = q.1.1) := by
        simpa [Sym2.eq_iff, Prod.ext_iff] using he
      rcases he' with h | h
      · refine ⟨(false, e), ?_⟩
        apply Subtype.ext
        exact Prod.ext h.1 h.2
      · refine ⟨(true, e), ?_⟩
        apply Subtype.ext
        exact Prod.ext h.2 h.1
  calc
    #{p : α × α // r p.fst p.snd} = #(Bool × fromRel sym) :=
      Cardinal.mk_congr (Equiv.ofBijective f hf).symm
    _ = 2 * #(fromRel sym) := by simp [Cardinal.mk_prod]
