/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_coeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 214
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
  ext n
  simp [ofCoeffList, coeffList, coeff_reverse, revAt,
    degree_eq_natDegree hP]
  change ((List.range (P.natDegree + 1)).map P.coeff).reverse[n]?.getD 0 =
    P.coeff (if n ≤ P.natDegree then P.natDegree - n else n)
  by_cases hn : n ≤ P.natDegree
  · have hlen :
        n < ((List.range (P.natDegree + 1)).map P.coeff).reverse.length := by
      simpa using Nat.lt_succ_of_le hn
    rw [List.getElem?_eq_getElem hlen]
    simp [List.getElem_reverse, hn]
  · have hlen :
        ((List.range (P.natDegree + 1)).map P.coeff).reverse.length ≤ n := by
      simpa using Nat.succ_le_of_lt (Nat.lt_of_not_ge hn)
    rw [List.getElem?_eq_none hlen]
    simp [hn, coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hn)]
