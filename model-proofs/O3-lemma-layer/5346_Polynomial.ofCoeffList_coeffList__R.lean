/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_coeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 214
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Polynomial
variable {R : Type*}
section Semiring
variable [Semiring R]
variable {P : R[X]}
variable (R) in

@[simp]
theorem ofCoeffList_coeffList (P : R[X]) : ofCoeffList P.coeffList = P.reverse := by
  ext n
  rcases eq_or_ne P 0 with rfl | hP
  · simp [coeffList, ofCoeffList]
  · rw [coeff_reverse, coeff_ofCoeffList]
    simp only [coeffList, degree_eq_natDegree hP]
    have hs : (List.range ((P.natDegree : WithBot ℕ).succ))
        = List.range (P.natDegree + 1) := rfl
    rw [hs]
    by_cases hn : n ≤ P.natDegree
    · rw [revAt_le hn]
      have h3 : P.natDegree - n < P.natDegree + 1 := by omega
      have h4 : n < P.natDegree + 1 := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_reverse, List.getElem?_map,
        List.getElem?_range, h3, h4]
      try (congr 1; omega)
    · push_neg at hn
      have hr : revAt P.natDegree n = n := by
        first
          | exact revAt_eq_self_of_lt hn
          | (show revAtFun _ _ = _; simp [revAtFun]; omega)
      rw [hr, coeff_eq_zero_of_natDegree_lt hn]
      first
        | (rw [List.getD_eq_default]; simp; omega)
        | (simp [List.getD_eq_getElem?_getD]; rw [List.getElem?_eq_none (by simp; omega)]; rfl)
        | (simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none]; omega)
