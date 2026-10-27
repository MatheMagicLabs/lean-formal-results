/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.coeff_ofCoeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 194
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm B, verified in round 0 (round 0 = first attempt)
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
theorem coeff_ofCoeffList (l : List R) (i : ℕ) : (ofCoeffList l).coeff i = l.getD i 0 := by
  induction l generalizing i with
  | nil =>
      simp [ofCoeffList]
  | cons a l ih =>
      cases i <;>
        simp [ofCoeffList, coeff_add, coeff_mul_X, coeff_X_mul, ih, List.getD]
