/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ofLists_transpose
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/OfLists.lean, line 78
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 3 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[simp]
theorem ofLists_transpose [Zero α] (m n : ℕ) (rows : List (List α)) :
    ofLists n m (ListMatrix.transpose n rows) = (ofLists m n rows)ᵀ := by
  ext i j
  simp only [transpose_apply, ofLists_apply, ofList_apply]
  have hlen : ∀ (row : List α) (cols : List (List α)),
      (ListMatrix.consPad row cols).length = cols.length := by
    intro row cols
    induction cols generalizing row with
    | nil => cases row <;> simp [ListMatrix.consPad]
    | cons c cols ih => cases row <;> simp [ListMatrix.consPad, ih]
  have hget : ∀ (row : List α) (cols : List (List α)) (i : ℕ), i < cols.length →
      (ListMatrix.consPad row cols).getD i [] = row.getD i 0 :: cols.getD i [] := by
    intro row cols
    induction cols generalizing row with
    | nil => intro i h; simp at h
    | cons c cols ih =>
      intro i h
      cases row <;> cases i <;>
        simp_all [ListMatrix.consPad, List.getD_eq_getElem?_getD, List.getElem?_map]
  have hT : ∀ rows : List (List α), (ListMatrix.transpose n rows).length = n := by
    intro rows
    induction rows with
    | nil => simp [ListMatrix.transpose]
    | cons r rs ih => simp [ListMatrix.transpose, hlen, ih]
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  simp only []
  clear hj
  induction rows generalizing j with
  | nil =>
    simp [ListMatrix.transpose, List.getD_eq_getElem?_getD, List.getElem?_replicate, hi]
  | cons row rows ih =>
    simp only [ListMatrix.transpose]
    rw [hget _ _ _ (by rw [hT]; exact hi)]
    cases j with
    | zero => simp
    | succ j => simpa [List.getD_eq_getElem?_getD] using ih j
