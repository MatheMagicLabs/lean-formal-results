/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.ofCoeffList_zipWithAll_add
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 247
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
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
theorem ofCoeffList_zipWithAll_add (p q : List R) :
    ofCoeffList (List.zipWithAll (fun a b => a.getD 0 + b.getD 0) p q) =
      ofCoeffList p + ofCoeffList q := by
  ext n
  simp only [coeff_add, coeff_ofCoeffList, List.getD_eq_getElem?_getD,
    List.getElem?_zipWithAll]
  rcases h : p[n]? with _ | a <;> rcases h' : q[n]? with _ | b <;> simp
