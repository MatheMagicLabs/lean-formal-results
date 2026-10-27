/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     map_ringInverse
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Units/Lemmas.lean, line 38
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem map_ringInverse [MonoidWithZeroHomClass F M₀ M₀'] (f : F) [IsLocalHom f] (a : M₀) :
    f a⁻¹ʳ = (f a)⁻¹ʳ := by
  by_cases h : IsUnit a
  · exact h.map_ringInverse f
  · have h' : ¬ IsUnit (f a) := fun h'' => h (isUnit_of_map_unit f a h'')
    rw [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ h', map_zero]
