/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_reverse_coeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 203
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 3 (round 0 = first attempt)
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
theorem ofCoeffList_reverse_coeffList (P : R[X]) : ofCoeffList P.coeffList.reverse = P := by
  classical
  by_cases hP : P = 0
  · subst P
    simp
  ext n
  by_cases hn : n ≤ P.natDegree
  · simp [coeffList, degree_eq_natDegree hP, Nat.lt_succ_iff, hn]
    change (Option.map P.coeff
      (List.range (P.natDegree + 1))[n]?).getD 0 = P.coeff n
    have h : n < P.natDegree + 1 := Nat.lt_succ_of_le hn
    simp [List.getElem?_range, h]
  · have hc : P.coeff n = 0 :=
      coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hn)
    simp [coeffList, degree_eq_natDegree hP, Nat.lt_succ_iff, hn, hc]
    change (Option.map P.coeff
      (List.range (P.natDegree + 1))[n]?).getD 0 = 0
    have h : (List.range (P.natDegree + 1)).length ≤ n := by
      simpa using Nat.lt_of_not_ge hn
    rw [List.getElem?_eq_none h]
    rfl
