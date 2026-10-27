/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     map_ringInverse
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Units/Lemmas.lean, line 38
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem map_ringInverse [MonoidWithZeroHomClass F M₀ M₀'] (f : F) [IsLocalHom f] (a : M₀) :
    f a⁻¹ʳ = (f a)⁻¹ʳ := by
  by_cases h : IsUnit a
  · exact h.map_ringInverse f
  · have hf : ¬ IsUnit (f a) := fun hfa => h (IsLocalHom.map_nonunit a hfa)
    rw [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ hf, map_zero]
