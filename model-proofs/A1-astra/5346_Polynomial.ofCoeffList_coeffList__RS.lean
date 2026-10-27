/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_coeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 214
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  ext i
  rw [coeff_ofCoeffList, coeffList_of_ne_zero hP, coeff_reverse]
  by_cases hi : i < P.natDegree + 1
  · have hi' : i ≤ P.natDegree := by omega
    simp [List.getD, List.getElem?_eq_getElem, hi, hi', revAt]
    change P.coeff (P.natDegree - i) =
      P.coeff (if i ≤ P.natDegree then P.natDegree - i else i)
    rw [if_pos hi']
  · have hi' : P.natDegree < i := by omega
    have hn : ¬ i ≤ P.natDegree := by omega
    simp [List.getD, List.getElem?_eq_getElem, hi, hn, revAt,
      coeff_eq_zero_of_natDegree_lt hi']
    change 0 = P.coeff (if i ≤ P.natDegree then P.natDegree - i else i)
    rw [if_neg hn, coeff_eq_zero_of_natDegree_lt hi']
