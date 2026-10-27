/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_zipWithAll_sub
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 280
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  induction p generalizing q with
  | nil =>
      induction q with
      | nil => simp [ofCoeffList, List.zipWithAll]
      | cons b q ih =>
          simp_all [ofCoeffList, List.zipWithAll, mul_sub, sub_mul]
          <;> simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  | cons a p ih =>
      cases q with
      | nil =>
          simp_all [ofCoeffList, List.zipWithAll, mul_sub, sub_mul]
          <;> simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      | cons b q =>
          simp_all [ofCoeffList, List.zipWithAll, mul_sub, sub_mul]
          <;> simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
