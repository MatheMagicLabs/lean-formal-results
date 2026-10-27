/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.coeff_ofCoeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 194
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 0 (round 0 = first attempt)
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

@[simp]
theorem coeff_ofCoeffList (l : List R) (i : ℕ) : (ofCoeffList l).coeff i = l.getD i 0 := by
  induction l generalizing i with
  | nil => simp
  | cons c l ih =>
      cases i with
      | zero => simp [ofCoeffList_cons]
      | succ i => simp [ofCoeffList_cons, ih]
