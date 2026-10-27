/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_le_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 119
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem cardinalMk_prod_le_two_mul_cardinalMk_fromRel :
    #{ p : α × α // r p.fst p.snd } ≤ 2 * #(fromRel sym) := by
  classical
  let f : {p : α × α // r p.1 p.2} → Bool × fromRel sym := fun p =>
    (decide (s(p.1.1, p.1.2).out.1 = p.1.1),
      ⟨s(p.1.1, p.1.2), Sym2.fromRel_prop.mpr p.2⟩)
  have hf : Function.Injective f := by
    rintro ⟨⟨a, b⟩, h⟩ ⟨⟨c, d⟩, h'⟩ heq
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    rw [h2] at h1
    simp only [decide_eq_decide] at h1
    have hm := Sym2.out_fst_mem s(c, d)
    rw [Sym2.mem_iff] at hm
    rcases Sym2.eq_iff.mp h2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · subst e1 e2
      rfl
    · have hac : a = c := by
        rcases hm with hm | hm
        · exact (h1.mpr hm).symm.trans hm
        · exact e1.trans (hm.symm.trans (h1.mp (hm.trans e1.symm)))
      have hbd : b = d := e2.trans (hac.symm.trans e1)
      subst hac hbd
      rfl
  have := Cardinal.mk_le_of_injective hf
  simpa using this
