/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_coeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 214
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[simp]
theorem ofCoeffList_coeffList (P : R[X]) : ofCoeffList P.coeffList = P.reverse := by
  by_cases h : P = 0
  · simp [h]
  ext i
  rw [coeff_ofCoeffList, coeffList_of_ne_zero h, coeff_reverse]
  rcases le_or_gt i P.natDegree with hi | hi
  · rw [revAt_le hi, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_reverse (by simp <;> omega), List.getElem?_range (by simp <;> omega)]
    all_goals simp
  · have hr : revAt P.natDegree i = i := by
      show (if i ≤ P.natDegree then P.natDegree - i else i) = i
      exact if_neg (Nat.not_le.mpr hi)
    rw [hr]
    rw [coeff_eq_zero_of_natDegree_lt hi, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by
        simp only [List.length_map, List.length_reverse, List.length_range]
        omega)]
    all_goals simp
