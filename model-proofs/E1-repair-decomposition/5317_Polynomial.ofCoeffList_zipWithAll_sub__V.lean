/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_zipWithAll_sub
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 280
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 2 (round 0 = first attempt)
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
      | nil => simp [List.zipWithAll]
      | cons b q ih =>
          simp_all [List.zipWithAll, ofCoeffList_cons, mul_sub, sub_mul,
            sub_eq_add_neg, mul_add, mul_neg, add_assoc, add_left_comm, add_comm]
  | cons a p ih =>
      cases q with
      | nil =>
          have h := ih []
          simp_all [List.zipWithAll, ofCoeffList_cons, mul_sub, sub_mul,
            sub_eq_add_neg, mul_add, mul_neg, add_assoc, add_left_comm, add_comm]
      | cons b q =>
          simp_all [List.zipWithAll, ofCoeffList_cons, mul_sub, sub_mul,
            sub_eq_add_neg, mul_add, mul_neg, add_assoc, add_left_comm, add_comm]
