/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.map_ofCoeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 227
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA3-leanstral-agent-feedback, arm rueck, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent with goal-state feedback (arm rueck)
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
  | nil => simp
  | cons c p ih =>
    simp [ofCoeffList_cons, map_add, map_mul, map_C, map_X, ih]
