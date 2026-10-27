/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ofLists_mul
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/OfLists.lean, line 84
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem ofLists_mul [Mul α] [AddCommMonoid α] {l m n : ℕ} {A B C : List (List α)}
    (h : ListMatrix.mul l m n A B = C) : ofLists l m A * ofLists m n B = ofLists l n C := by
  subst h
  ext i k
  have hB : (fun j => ofLists m n B j k) = ofLists n m (ListMatrix.transpose n B) k := by
    rw [ofLists_transpose]; rfl
  rw [Matrix.mul_apply', hB]
  show ofLists l m A i ⬝ᵥ ofLists n m (ListMatrix.transpose n B) k = _
  rw [ofLists_apply, ofLists_apply, ofLists_apply, ← ListMatrix.dotProduct_eq]
  first
    | simpa using (ListMatrix.getD_mul A B i.isLt k.isLt).symm
    | simp [ListMatrix.getD_mul, i.isLt, k.isLt]
    | simpa using (ListMatrix.mul_getD A B i.isLt k.isLt).symm
    | simp [ListMatrix.mul_getD, i.isLt, k.isLt]
    | simp [ListMatrix.mul, i.isLt, k.isLt]
