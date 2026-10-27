/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_map_mul
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 238
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
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
  first
  | (ext n
     rw [coeff_C_mul]
     simp [coeff_ofCoeffList, List.getD_eq_getElem?_getD, List.getElem?_map] <;>
     (cases h : l[n]? <;> simp_all))
  | (ext n
     rw [coeff_C_mul]
     simp_all [coeff_ofCoeffList, List.getD_eq_getElem?_getD, List.getElem?_map] <;>
     (cases h : l[n]? <;> simp_all))
  | (induction l with
     | nil => simp [ofCoeffList]
     | cons b l ih =>
       simp_all [ofCoeffList, C_mul] <;>
       first
       | ring
       | (simp [mul_add, mul_left_comm, mul_assoc, ← C_mul] ))
