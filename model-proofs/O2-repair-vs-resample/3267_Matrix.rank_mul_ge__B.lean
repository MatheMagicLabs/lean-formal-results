/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Matrix.rank_mul_ge
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/Matrix/Rank.lean, line 198
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem rank_mul_ge [CommRing R] [IsDomain R] (A : Matrix m n R) (B : Matrix n o R) :
    A.rank + B.rank ≤ (A * B).rank + Fintype.card n := by
  classical
  have h1 := LinearMap.finrank_range_add_finrank_ker
    (A.mulVecLin.domRestrict (LinearMap.range B.mulVecLin))
  have h2 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have h3 : LinearMap.range (A.mulVecLin.domRestrict (LinearMap.range B.mulVecLin)) =
      LinearMap.range (A * B).mulVecLin := by
    rw [mulVecLin_mul, LinearMap.range_comp, LinearMap.range_domRestrict]
  have h4 : finrank R (LinearMap.ker (A.mulVecLin.domRestrict (LinearMap.range B.mulVecLin)))
      ≤ finrank R (LinearMap.ker A.mulVecLin) := by
    rw [(Submodule.equivMapOfInjective (LinearMap.range B.mulVecLin).subtype
      (Submodule.injective_subtype _) _).finrank_eq]
    refine finrank_le_finrank_of_rank_le_rank
      (Cardinal.lift_le.mpr (Submodule.rank_mono ?_))
      ((Submodule.rank_le _).trans_lt (rank_lt_aleph0 R (n → R)))
    rintro _ ⟨x, hx, rfl⟩
    simpa [LinearMap.mem_ker] using hx
  rw [finrank_pi R] at h2
  rw [rank, rank, rank, ← h3]
  omega
