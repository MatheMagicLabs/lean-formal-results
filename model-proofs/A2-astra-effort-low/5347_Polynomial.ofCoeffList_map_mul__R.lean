/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_map_mul
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 238
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 2 (round 0 = first attempt)
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
theorem ofCoeffList_map_mul (a : R) (l : List R) :
    ofCoeffList (l.map (a * ·)) = C a * ofCoeffList l := by
  induction l with
  | nil => simp [ofCoeffList]
  | cons b l ih =>
      simp only [List.map_cons, ofCoeffList_cons, ih]
      simp only [map_mul, mul_add, ← mul_assoc]
      rw [show X * C a = C a * X from X_mul]
