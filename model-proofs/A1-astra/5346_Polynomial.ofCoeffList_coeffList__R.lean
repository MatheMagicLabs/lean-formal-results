/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_coeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 214
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 2 (round 0 = first attempt)
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
  ext n
  by_cases hP : P = 0
  · subst P
    simp
  · have hdeg : P.degree.succ = P.natDegree + 1 := by
      rw [degree_eq_natDegree hP]
      rfl
    by_cases hn : n ≤ P.natDegree
    · have hi : P.natDegree - n < P.natDegree + 1 := by omega
      simp [coeff_ofCoeffList, coeffList, coeff_reverse, hdeg,
        List.getElem?_reverse, hn, hi, Nat.lt_succ_iff]
    · have hz : P.coeff n = 0 :=
        coeff_eq_zero_of_natDegree_lt (by omega)
      simp [coeff_ofCoeffList, coeffList, coeff_reverse, hdeg,
        List.getElem?_reverse, revAt, hn, hz, Nat.lt_succ_iff]
      change 0 = P.coeff (if n ≤ P.natDegree then P.natDegree - n else n)
      simp [hn, hz]
