/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_coeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 214
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[simp]
theorem ofCoeffList_coeffList (P : R[X]) : ofCoeffList P.coeffList = P.reverse := by
  by_cases hP : P = 0
  · simp [hP]
  ext i
  rw [coeff_ofCoeffList, coeff_reverse, coeffList_of_ne_zero hP]
  by_cases hi : i ≤ P.natDegree
  · rw [revAt_le hi, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_reverse (by simpa using Nat.lt_succ_of_le hi), List.length_range,
      List.getElem?_range (by lia)]
    all_goals simp
  · push_neg at hi
    rw [revAt_eq_self_of_lt hi, coeff_eq_zero_of_natDegree_lt hi, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; lia)]
    all_goals simp
