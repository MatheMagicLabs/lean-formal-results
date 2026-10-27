/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_le_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 119
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem cardinalMk_prod_le_two_mul_cardinalMk_fromRel :
    #{ p : α × α // r p.fst p.snd } ≤ 2 * #(fromRel sym) := by
  classical
  have key : #{p : α × α // r p.fst p.snd} ≤ #(Bool × fromRel sym) := by
    refine Cardinal.mk_le_of_injective
      (f := fun p => (decide (p.1.1 = (s(p.1.1, p.1.2)).out.fst),
        ⟨s(p.1.1, p.1.2), Sym2.fromRel_prop.mpr p.2⟩)) ?_
    intro ⟨⟨a, b⟩, h⟩ ⟨⟨c, d⟩, h'⟩ heq
    simp only [Prod.mk.injEq, Subtype.mk.injEq, decide_eq_decide] at heq
    obtain ⟨h1, h3⟩ := heq
    have hm := Sym2.out_fst_mem s(a, b)
    rw [← h3] at h1
    rw [Sym2.eq_iff] at h3
    rcases h3 with ⟨hac, hbd⟩ | ⟨had, hbc⟩
    · subst hac
      subst hbd
      rfl
    · have hab : a = b := by
        rcases Sym2.mem_iff.mp hm with h4 | h4
        · have h5 := h1.mp h4.symm
          exact h4.symm.trans (h5.symm.trans hbc.symm)
        · have hc : c = (s(a, b)).out.fst := hbc.symm.trans h4.symm
          exact (h1.mpr hc).trans h4
      subst hab
      subst had
      subst hbc
      rfl
  simpa [Cardinal.mk_prod] using key
