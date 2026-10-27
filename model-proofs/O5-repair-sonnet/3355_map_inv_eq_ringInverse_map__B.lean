/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     map_inv_eq_ringInverse_map
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Units/Lemmas.lean, line 72
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem map_inv_eq_ringInverse_map [FunLike F G₀ M₀]
    [MonoidWithZeroHomClass F G₀ M₀] (f : F) (a : G₀) :
    f a⁻¹ = (f a)⁻¹ʳ := by
  by_cases ha : a = 0
  · subst ha
    simp
  · rw [← Ring.inverse_eq_inv, IsUnit.map_ringInverse f (isUnit_iff_ne_zero.2 ha)]
