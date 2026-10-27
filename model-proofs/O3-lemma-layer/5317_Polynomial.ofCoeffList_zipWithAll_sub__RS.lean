/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_zipWithAll_sub
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 280
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 3 (round 0 = first attempt)
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
end Semiring
section Ring
variable [Ring R] (P : R[X])

@[simp]
theorem ofCoeffList_zipWithAll_sub (p q : List R) :
    ofCoeffList (List.zipWithAll (fun a b => a.getD 0 - b.getD 0) p q) =
      ofCoeffList p - ofCoeffList q := by
  have h0 : ∀ q : List R,
      ofCoeffList (List.zipWithAll (fun a b => a.getD 0 - b.getD 0) [] q) =
        - ofCoeffList q := by
    intro q
    induction q with
    | nil => simp [List.zipWithAll]
    | cons b q ih =>
      simp [List.zipWithAll, ofCoeffList_cons, mul_neg, ih, add_comm]
  induction p generalizing q with
  | nil =>
    simpa [sub_eq_add_neg] using h0 q
  | cons a p ih =>
    cases q with
    | nil =>
      simp [List.zipWithAll, ofCoeffList_cons, mul_sub, mul_add, mul_neg, ih,
        sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    | cons b q =>
      simp [List.zipWithAll, ofCoeffList_cons, ih, mul_sub, C_sub]
      try simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
