/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Matrix.mulVec_surjective_iff_rank_eq_card
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/Matrix/Rank.lean, line 591
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem mulVec_surjective_iff_rank_eq_card [Field R] [Fintype m] {M : Matrix m n R} :
    M.mulVec.Surjective ↔ M.rank = Fintype.card m := by
  have h : M.mulVec.Surjective ↔ LinearMap.range M.mulVecLin = ⊤ :=
    (LinearMap.range_eq_top (f := M.mulVecLin)).symm
  rw [h, rank]
  constructor
  · intro h1
    rw [h1, finrank_top, Module.finrank_fintype_fun_eq_card]
  · intro h2
    apply Submodule.eq_top_of_finrank_eq
    rw [h2, Module.finrank_fintype_fun_eq_card]
