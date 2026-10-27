/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.finite_fromRel_iff
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 140
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem finite_fromRel_iff : (fromRel sym).Finite ↔ Finite { p : α × α // r p.fst p.snd } := by
  constructor
  · intro h
    have h' := h.to_subtype
    rw [← Cardinal.lt_aleph0_iff_finite] at h' ⊢
    calc _ ≤ 2 * #(fromRel sym) := cardinalMk_prod_le_two_mul_cardinalMk_fromRel sym
      _ < Cardinal.aleph0 := Cardinal.mul_lt_aleph0 (by simp) h'
  · intro h
    rw [← Set.finite_coe_iff, ← Cardinal.lt_aleph0_iff_finite]
    refine lt_of_le_of_lt (Cardinal.mk_le_of_surjective
      (f := fun p : { p : α × α // r p.fst p.snd } =>
        (⟨s(p.1.1, p.1.2), by simpa using p.2⟩ : fromRel sym)) ?_)
      (Cardinal.lt_aleph0_iff_finite.mpr h)
    rintro ⟨z, hz⟩
    induction z using Sym2.ind
    rename_i a b
    exact ⟨⟨(a, b), by simpa using hz⟩, rfl⟩
