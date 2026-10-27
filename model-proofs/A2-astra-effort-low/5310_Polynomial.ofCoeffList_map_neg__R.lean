/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_map_neg
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 274
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 1 (round 0 = first attempt)
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
end Semiring
section Ring
variable [Ring R] (P : R[X])

@[simp]
theorem ofCoeffList_map_neg (l : List R) : ofCoeffList (l.map (-·)) = -ofCoeffList l := by
  induction l with
  | nil => simp [ofCoeffList]
  | cons a l ih =>
      simp_all [ofCoeffList, mul_neg, neg_mul, neg_add, add_comm]
