/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ofLists_mul
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/OfLists.lean, line 84
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem ofLists_mul [Mul α] [AddCommMonoid α] {l m n : ℕ} {A B C : List (List α)}
    (h : ListMatrix.mul l m n A B = C) : ofLists l m A * ofLists m n B = ofLists l n C := by
  subst h
  ext i j
  have hB : ∀ k, ofLists m n B k j = ofLists n m (ListMatrix.transpose n B) j k := fun k => by
    rw [ofLists_transpose]; rfl
  rw [mul_apply']
  simp only [hB, ofLists_apply]
  rw [← ListMatrix.dotProduct_eq, ofList_apply]
  first
  | exact (ListMatrix.getD_mul A B i.isLt j.isLt).symm
  | (rw [ListMatrix.getD_mul _ _ i.isLt j.isLt]; done)
  | (rw [ListMatrix.getD_mul _ _ _ i.isLt j.isLt]; done)
  | (rw [ListMatrix.getD_mul]; done)
  | (simp only [ListMatrix.mul]; simp [i.isLt, j.isLt]; done)
  | (unfold ListMatrix.mul; simp [i.isLt, j.isLt]; done)
  | simp [ListMatrix.mul, ListMatrix.getD_mul, i.isLt, j.isLt]
