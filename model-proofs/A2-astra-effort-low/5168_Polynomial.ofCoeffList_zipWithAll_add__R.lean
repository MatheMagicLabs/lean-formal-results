/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_zipWithAll_add
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 247
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

@[simp]
theorem ofCoeffList_zipWithAll_add (p q : List R) :
    ofCoeffList (List.zipWithAll (fun a b => a.getD 0 + b.getD 0) p q) =
      ofCoeffList p + ofCoeffList q := by
  induction p generalizing q with
  | nil =>
      induction q with
      | nil => simp [List.zipWithAll, ofCoeffList]
      | cons b q ih =>
          simp_all [List.zipWithAll, ofCoeffList]
  | cons a p ih =>
      cases q with
      | nil =>
          simpa [List.zipWithAll, ofCoeffList] using
            congrArg (fun f : R[X] => C a + X * f) (ih [])
      | cons b q =>
          simp_all [List.zipWithAll, ofCoeffList, mul_add, add_mul,
            add_assoc, add_left_comm, add_comm]
