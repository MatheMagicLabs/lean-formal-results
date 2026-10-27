/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_coeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 214
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[simp]
theorem ofCoeffList_coeffList (P : R[X]) : ofCoeffList P.coeffList = P.reverse := by
  ext i
  by_cases hP : P = 0
  · subst hP
    simp
  rw [coeff_ofCoeffList, coeffList_of_ne_zero hP, coeff_reverse]
  by_cases h : i ≤ P.natDegree
  · rw [revAt_le h, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_reverse (by simp only [List.length_range]; omega),
      List.getElem?_range (by simp only [List.length_range]; omega)]
    simp
  · have h' : P.natDegree < i := by omega
    rw [revAt_eq_self_of_lt h', coeff_eq_zero_of_natDegree_lt h', List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp only [List.length_map, List.length_reverse, List.length_range]; omega)]
    simp
