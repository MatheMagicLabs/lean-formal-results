/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_reverse_coeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 203
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[simp]
theorem ofCoeffList_reverse_coeffList (P : R[X]) : ofCoeffList P.coeffList.reverse = P := by
  ext i
  rw [coeff_ofCoeffList]
  by_cases hP : P = 0
  · subst hP; simp
  rw [coeffList_of_ne_zero hP]
  simp only [List.map_reverse, List.reverse_reverse]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hi : i < P.natDegree + 1
  · rw [List.getElem?_range hi]
    simp
  · rw [List.getElem?_eq_none (by simp only [List.length_range]; omega)]
    simp only [Option.map_none, Option.getD_none]
    exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
