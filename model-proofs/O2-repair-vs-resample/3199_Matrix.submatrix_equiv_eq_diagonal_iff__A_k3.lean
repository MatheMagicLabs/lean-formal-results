/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Matrix.submatrix_equiv_eq_diagonal_iff
Source:      Mathlib @ a02a63c2, Mathlib/Data/Matrix/Diagonal.lean, line 430
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[simp]
theorem submatrix_equiv_eq_diagonal_iff [Zero α] [DecidableEq m] [DecidableEq l]
    {A : Matrix m m α} {e : l ≃ m} {d : l → α} :
    A.submatrix e e = diagonal d ↔ A = diagonal (d ∘ e.symm) := by
  constructor
  · intro h
    ext i j
    have := congrFun (congrFun h (e.symm i)) (e.symm j)
    simpa [diagonal_apply, submatrix_apply] using this
  · rintro rfl
    ext i j
    simp [diagonal_apply, submatrix_apply]
