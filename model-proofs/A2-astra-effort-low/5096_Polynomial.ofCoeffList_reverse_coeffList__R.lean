/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_reverse_coeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 203
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
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
  classical
  by_cases hP : P = 0
  · subst P
    simp
  have hd : P.degree.succ = P.natDegree + 1 := by
    rw [degree_eq_natDegree hP]
    rfl
  ext n
  by_cases hn : n ≤ P.natDegree
  · simp [coeffList, hd, getElem?_pos, Nat.lt_succ_iff, hn]
  · have hz : P.coeff n = 0 :=
      coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hn)
    simp [coeffList, hd, getElem?_neg, Nat.lt_succ_iff, hn, hz]
