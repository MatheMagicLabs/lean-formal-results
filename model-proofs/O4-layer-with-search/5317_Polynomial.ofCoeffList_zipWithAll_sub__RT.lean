/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_zipWithAll_sub
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 280
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
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
  have key : ∀ p q : List R,
      List.zipWithAll (fun a b => a.getD 0 - b.getD 0) p q =
        List.zipWithAll (fun a b => a.getD 0 + b.getD 0) p (q.map (-·)) := by
    intro p q
    induction p generalizing q with
    | nil =>
      induction q with
      | nil => rfl
      | cons b q ih => simp_all [List.zipWithAll, sub_eq_add_neg]
    | cons a p ih =>
      cases q with
      | nil => simp [List.zipWithAll, sub_eq_add_neg]
      | cons b q =>
        simp only [List.zipWithAll, List.map_cons, ← ih]
        simp [sub_eq_add_neg]
  rw [key, ofCoeffList_zipWithAll_add, ofCoeffList_map_neg, sub_eq_add_neg]
