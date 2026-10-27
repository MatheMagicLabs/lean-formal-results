/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_reverse_coeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 203
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
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
  ext i
  rw [coeff_ofCoeffList]
  by_cases hP : P = 0
  · subst hP; simp
  rw [coeffList_of_ne_zero hP, ← List.map_reverse, List.reverse_reverse]
  by_cases hi : i < P.natDegree + 1
  · simp [List.getD_eq_getElem?_getD, hi]
  · have : P.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    simp [List.getD_eq_getElem?_getD, hi, this]
