/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_coeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 214
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 3 (round 0 = first attempt)
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
theorem ofCoeffList_coeffList (P : R[X]) : ofCoeffList P.coeffList = P.reverse := by
  classical
  by_cases hP : P = 0
  · subst P
    simp
  · ext n
    simp only [coeff_ofCoeffList, coeffList, degree_eq_natDegree hP,
      coeff_reverse, List.map_reverse]
    change
      (List.map P.coeff (List.range (P.natDegree + 1))).reverse.getD n 0 =
        P.coeff (if n ≤ P.natDegree then P.natDegree - n else n)
    by_cases hn : n ≤ P.natDegree
    · simp [List.getElem?_reverse, Nat.lt_succ_iff, hn]
    · simp [List.getElem?_reverse, Nat.lt_succ_iff, hn,
        coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hn)]
