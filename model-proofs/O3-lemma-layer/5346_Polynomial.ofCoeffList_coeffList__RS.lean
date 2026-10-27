/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_coeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 214
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 2 (round 0 = first attempt)
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
  ext i
  rw [coeff_ofCoeffList, coeff_reverse]
  by_cases hP : P = 0
  · subst hP; simp
  · rw [coeffList_of_ne_zero hP, List.getD_eq_getElem?_getD]
    by_cases hi : i ≤ P.natDegree
    · rw [revAt_le hi]
      rw [List.getElem?_eq_getElem (by simp; omega)]
      simp only [Option.getD_some, List.getElem_map, List.getElem_reverse,
        List.getElem_range, List.length_range]
      try congr 1
      try omega
    · rw [List.getElem?_eq_none (by simp; omega)]
      have : revAt P.natDegree i = i := by
        first
          | exact revAt_eq_self_of_lt (by omega)
          | (show (if i ≤ P.natDegree then P.natDegree - i else i) = i
             rw [if_neg hi])
      rw [this, coeff_eq_zero_of_natDegree_lt (by omega)]
      try rfl
