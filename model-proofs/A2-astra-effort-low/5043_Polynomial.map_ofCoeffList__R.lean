/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.map_ofCoeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 227
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 0 (round 0 = first attempt)
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

theorem map_ofCoeffList {S : Type*} [Semiring S] (f : R →+* S) (l : List R) :
    (ofCoeffList l).map f = ofCoeffList (l.map f) := by
  induction l with
  | nil => simp [ofCoeffList]
  | cons a l ih =>
      simp_all [ofCoeffList, map_add, map_mul]
