/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_reverse_coeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 203
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
theorem ofCoeffList_reverse_coeffList (P : R[X]) : ofCoeffList P.coeffList.reverse = P := by
  by_cases hP : P = 0
  · subst P
    simp
  · rw [coeffList_of_ne_zero hP, ← List.map_reverse, List.reverse_reverse]
    ext i
    rw [coeff_ofCoeffList]
    by_cases hi : i < P.natDegree + 1
    · simp [List.getD, hi]
    · have hcoeff : P.coeff i = 0 :=
        coeff_eq_zero_of_natDegree_lt (by omega)
      simp [List.getD, hi, hcoeff]
