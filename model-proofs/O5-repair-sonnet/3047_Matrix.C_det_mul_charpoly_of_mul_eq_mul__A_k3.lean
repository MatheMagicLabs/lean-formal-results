/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Matrix.C_det_mul_charpoly_of_mul_eq_mul
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean, line 301
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem C_det_mul_charpoly_of_mul_eq_mul {A B P : Matrix n n R} (h : A * P = P * B) :
    C P.det * A.charpoly = C P.det * B.charpoly := by
  have h' := charmatrix_mul_map_C_of_mul_eq_mul h
  have hdet := congrArg Matrix.det h'
  rw [det_mul, det_mul] at hdet
  have hC : (P.map C).det = C P.det := (RingHom.map_det C P).symm
  rw [hC] at hdet
  simp only [charpoly]
  rw [mul_comm]
  exact hdet
