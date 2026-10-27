/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_zipWithAll_sub
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 280
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA2-leanstral-agent-variants, arm neu, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent on the 29 theorems O3LA left open: neu = fresh restart, fest = fixed instruction, staffel = staged budget
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
  | nil => simp
  | cons c p ih =>
    cases q with
    | nil => simp
    | cons d q =>
      simp [ofCoeffList_cons, List.zipWithAll_cons_cons]
      rw [ih q]
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, mul_neg]
