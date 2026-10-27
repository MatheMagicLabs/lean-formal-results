/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.map_ofCoeffList
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/CoeffList.lean, line 227
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem map_ofCoeffList {S : Type*} [Semiring S] (f : R →+* S) (l : List R) :
    (ofCoeffList l).map f = ofCoeffList (l.map f) := by
  induction l with
  | nil => simp
  | cons c p ih =>
    simp [ofCoeffList_cons, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, ih]
