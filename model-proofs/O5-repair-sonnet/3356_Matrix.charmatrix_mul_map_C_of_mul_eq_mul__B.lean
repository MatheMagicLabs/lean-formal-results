/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Matrix.charmatrix_mul_map_C_of_mul_eq_mul
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean, line 115
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 2 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma charmatrix_mul_map_C_of_mul_eq_mul {A : Matrix n n R} {B : Matrix m m R} {P : Matrix n m R}
    (h : A * P = P * B) : charmatrix A * P.map C = P.map C * charmatrix B := by
  have h1 : (scalar n (X : R[X])) * P.map C = P.map C * (scalar m (X : R[X])) := by
    rw [scalar_apply, scalar_apply]
    refine Matrix.ext fun i j => ?_
    rw [diagonal_mul, mul_diagonal]
    exact mul_comm _ _
  have h2 : ((C : R →+* R[X]).mapMatrix A) * P.map C
      = P.map C * ((C : R →+* R[X]).mapMatrix B) := by
    simp only [RingHom.mapMatrix_apply]
    rw [← Matrix.map_mul, ← Matrix.map_mul, h]
  rw [charmatrix, charmatrix, Matrix.sub_mul, Matrix.mul_sub, h1, h2]
