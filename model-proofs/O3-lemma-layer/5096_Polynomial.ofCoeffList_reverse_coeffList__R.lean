/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_reverse_coeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 203
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
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
theorem ofCoeffList_reverse_coeffList (P : R[X]) : ofCoeffList P.coeffList.reverse = P := by
  ext n
  by_cases hP : P = 0
  · subst hP
    simp [ofCoeffList, coeffList]
  · have hd : P.degree.succ = P.natDegree + 1 := by
      rw [degree_eq_natDegree hP]
      rfl
    by_cases h : n < P.natDegree + 1
    · simp only [ofCoeffList, coeffList] at *
      first
        | simp [hd, h, List.getElem?_range]
        | (rw [hd]; simp [h])
        | (rw [hd, List.getElem?_range h]; simp)
    · have h0 : P.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      have h' : P.natDegree + 1 ≤ n := by omega
      simp only [ofCoeffList, coeffList] at *
      first
        | (rw [hd, List.getElem?_eq_none (by simp; omega)]; simp [h0])
        | simp [hd, h, h', h0, List.getElem?_range]
        | (rw [hd]; simp [h', h0])
