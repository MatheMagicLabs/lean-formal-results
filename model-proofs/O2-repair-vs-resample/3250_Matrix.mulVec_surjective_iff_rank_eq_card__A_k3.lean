/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Matrix.mulVec_surjective_iff_rank_eq_card
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/Matrix/Rank.lean, line 591
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem mulVec_surjective_iff_rank_eq_card [Field R] [Fintype m] {M : Matrix m n R} :
    M.mulVec.Surjective ↔ M.rank = Fintype.card m := by
  have hs : M.mulVec.Surjective ↔ Function.Surjective M.mulVecLin := Iff.rfl
  rw [hs, ← LinearMap.range_eq_top, rank]
  constructor
  · intro h
    rw [h, finrank_top, Module.finrank_fintype_fun_eq_card]
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    rw [h, Module.finrank_fintype_fun_eq_card]
