/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.finite_fromRel_iff
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 140
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem finite_fromRel_iff : (fromRel sym).Finite ↔ Finite { p : α × α // r p.fst p.snd } := by
  constructor
  · intro h
    have := h.to_subtype
    rw [← Cardinal.lt_aleph0_iff_finite] at this ⊢
    refine (cardinalMk_prod_le_two_mul_cardinalMk_fromRel sym).trans_lt ?_
    exact Cardinal.mul_lt_aleph0 (by simpa using Cardinal.nat_lt_aleph0 2) this
  · intro h
    refine Set.finite_coe_iff.mp ?_
    refine Finite.of_surjective
      (fun p : {p : α × α // r p.1 p.2} =>
        (⟨s(p.1.1, p.1.2), by simpa using p.2⟩ : fromRel sym)) ?_
    rintro ⟨z, hz⟩
    revert hz
    induction z using Sym2.ind
    rename_i x y
    intro hz
    exact ⟨⟨(x, y), by simpa using hz⟩, rfl⟩
