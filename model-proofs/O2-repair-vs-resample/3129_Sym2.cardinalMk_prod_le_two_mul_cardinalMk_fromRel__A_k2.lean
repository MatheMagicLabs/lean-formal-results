/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_le_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 119
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem cardinalMk_prod_le_two_mul_cardinalMk_fromRel :
    #{ p : α × α // r p.fst p.snd } ≤ 2 * #(fromRel sym) := by
  classical
  let f : { p : α × α // r p.fst p.snd } → Bool × fromRel sym := fun p =>
    (decide (s(p.1.1, p.1.2).out.1 = p.1.1), ⟨s(p.1.1, p.1.2), by simpa using p.2⟩)
  have hf : Function.Injective f := by
    rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨c, d⟩, hcd⟩ h
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq, decide_eq_decide] at h
    obtain ⟨h1, h2⟩ := h
    rw [Sym2.eq_iff] at h2
    rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · rw [Sym2.eq_swap (a := b)] at h1
      have hm : s(a, b).out.1 = a ∨ s(a, b).out.1 = b :=
        Sym2.mem_iff.mp (Sym2.out_fst_mem _)
      have hab' : a = b := by
        rcases hm with hm | hm
        · exact hm.symm.trans (h1.mp hm)
        · exact (h1.mpr hm).symm.trans hm
      subst hab'
      rfl
  refine (Cardinal.mk_le_of_injective hf).trans_eq ?_
  simp [Cardinal.mk_prod]
