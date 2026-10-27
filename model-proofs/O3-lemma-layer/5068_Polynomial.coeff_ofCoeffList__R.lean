/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.coeff_ofCoeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 194
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
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
theorem coeff_ofCoeffList (l : List R) (i : ℕ) : (ofCoeffList l).coeff i = l.getD i 0 := by
  first
  | (induction l generalizing i with
      | nil => simp [ofCoeffList]
      | cons a l ih =>
        cases i <;> simp_all [ofCoeffList, coeff_C, coeff_X_mul, coeff_add, coeff_C_mul])
  | (simp only [ofCoeffList, finset_sum_coeff, coeff_monomial]
     by_cases h : i < l.length <;>
       simp_all [List.getD_eq_default, Finset.sum_ite_eq', Finset.sum_ite_eq, List.getD_eq_getElem])
