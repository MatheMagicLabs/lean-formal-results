/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_coeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 214
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[simp]
theorem ofCoeffList_coeffList (P : R[X]) : ofCoeffList P.coeffList = P.reverse := by
  ext i
  rw [coeff_ofCoeffList, coeff_reverse]
  by_cases hP : P = 0
  · simp [hP]
  rw [coeffList_of_ne_zero hP]
  rcases le_or_gt i P.natDegree with h | h
  · rw [revAt_le h]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_reverse (by simp; omega), List.length_range,
      List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some, Nat.add_sub_cancel]
  · rw [revAt_eq_self_of_lt h, coeff_eq_zero_of_natDegree_lt h,
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    rfl
