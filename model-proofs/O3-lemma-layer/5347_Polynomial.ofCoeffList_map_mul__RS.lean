/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_map_mul
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 238
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
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
theorem ofCoeffList_map_mul (a : R) (l : List R) :
    ofCoeffList (l.map (a * ·)) = C a * ofCoeffList l := by
  induction l with
  | nil => simp [ofCoeffList_nil]
  | cons c l ih =>
    simp only [List.map_cons, ofCoeffList_cons, ih, C_mul, mul_add]
    rw [← mul_assoc, ← mul_assoc, X_mul_C]
