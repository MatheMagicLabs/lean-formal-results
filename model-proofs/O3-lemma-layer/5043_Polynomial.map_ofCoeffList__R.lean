/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.map_ofCoeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 227
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

theorem map_ofCoeffList {S : Type*} [Semiring S] (f : R →+* S) (l : List R) :
    (ofCoeffList l).map f = ofCoeffList (l.map f) := by
  first
  | (induction l with
      | nil => simp [ofCoeffList]
      | cons a l ih => simp_all [ofCoeffList])
  | (ext n
     simp only [coeff_map, coeff_ofCoeffList]
     simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
     cases l[n]? <;> simp)
  | (ext n
     simp [ofCoeffList, coeff_map])
