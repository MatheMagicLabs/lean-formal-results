/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_reverse_coeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 203
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  ext n
  by_cases hn : n ≤ P.natDegree
  · simp_all [coeffList, degree_eq_natDegree hP, Nat.lt_succ_iff]
    change (Option.map P.coeff (List.range (P.natDegree + 1))[n]?).getD 0 =
      P.coeff n
    have hi : n < (List.range (P.natDegree + 1)).length := by
      simpa using Nat.lt_succ_of_le hn
    rw [List.getElem?_eq_getElem hi]
    simp
  · have hz : P.coeff n = 0 :=
      coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hn)
    simp_all [coeffList, degree_eq_natDegree hP, Nat.lt_succ_iff]
    change (Option.map P.coeff (List.range (P.natDegree + 1))[n]?).getD 0 = 0
    have hi : (List.range (P.natDegree + 1)).length ≤ n := by
      simp only [List.length_range]
      omega
    simp_all
