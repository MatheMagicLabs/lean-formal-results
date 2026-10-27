/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Matrix.charmatrix_mul_map_C_of_mul_eq_mul
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean, line 115
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 3 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma charmatrix_mul_map_C_of_mul_eq_mul {A : Matrix n n R} {B : Matrix m m R} {P : Matrix n m R}
    (h : A * P = P * B) : charmatrix A * P.map C = P.map C * charmatrix B := by
  rw [charmatrix, charmatrix, Matrix.sub_mul, Matrix.mul_sub, RingHom.mapMatrix_apply,
    RingHom.mapMatrix_apply, ← Matrix.map_mul, ← Matrix.map_mul, h]
  congr 1
  ext i j
  simp only [scalar_apply, diagonal_mul, mul_diagonal, map_apply]
  all_goals first
    | exact (commute_X _).eq
    | exact (commute_X _).eq.symm
    | simp [X_mul]
