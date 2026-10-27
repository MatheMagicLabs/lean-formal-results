/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Matrix.C_det_mul_charpoly_of_mul_eq_mul
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean, line 301
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem C_det_mul_charpoly_of_mul_eq_mul {A B P : Matrix n n R} (h : A * P = P * B) :
    C P.det * A.charpoly = C P.det * B.charpoly := by
  have h' := congrArg det (charmatrix_mul_map_C_of_mul_eq_mul h)
  rw [det_mul, det_mul] at h'
  have hP : (P.map C).det = C P.det := (RingHom.map_det _ _).symm
  rw [hP] at h'
  calc C P.det * A.charpoly = det (charmatrix A) * C P.det := mul_comm _ _
    _ = C P.det * det (charmatrix B) := h'
