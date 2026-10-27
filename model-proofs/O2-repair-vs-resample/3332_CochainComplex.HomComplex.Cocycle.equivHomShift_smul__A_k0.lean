/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CochainComplex.HomComplex.Cocycle.equivHomShift_smul
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Homology/HomotopyCategory/HomComplexShift.lean, line 565
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[simp]
lemma equivHomShift_smul (r : R) (z : K ⟶ L⟦n⟧) :
    equivHomShift (r • z) = r • equivHomShift z := by
  ext p q hpq
  simp [equivHomShift_apply, Cochain.rightUnshift_v _ _ _ _ _ _ _ (add_zero p)]
