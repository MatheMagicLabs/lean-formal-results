/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsAlgClosed.isSquare
Source:      Mathlib @ a02a63c2, Mathlib/FieldTheory/IsAlgClosed/Basic.lean, line 91
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem isSquare [IsAlgClosed k] (x : k) : IsSquare x := by
  obtain ⟨z, hz⟩ := exists_pow_nat_eq x (n := 2) (by norm_num)
  exact ⟨z, by rw [← hz, sq]⟩
