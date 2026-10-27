/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_coeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 214
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[simp]
theorem ofCoeffList_coeffList (P : R[X]) : ofCoeffList P.coeffList = P.reverse := by
  by_cases h : P = 0
  · subst h
    simp
  ext i
  rw [coeff_ofCoeffList, coeff_reverse, coeffList_of_ne_zero h]
  by_cases hi : i ≤ P.natDegree
  · rw [revAt_le hi, List.getD_eq_getElem?_getD, List.map_reverse,
      List.getElem?_reverse (by simp only [List.length_map, List.length_range]; omega),
      List.getElem?_map, List.length_map, List.length_range,
      List.getElem?_range (by omega)]
    simp
  · push_neg at hi
    have h2 : revAt P.natDegree i = i := by
      show (if i ≤ P.natDegree then P.natDegree - i else i) = i
      rw [if_neg (not_le.mpr hi)]
    rw [h2, coeff_eq_zero_of_natDegree_lt hi, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp only [List.length_map, List.length_reverse, List.length_range]; omega)]
    simp
