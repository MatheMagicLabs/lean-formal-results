/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     map_inv_eq_ringInverse_map
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Units/Lemmas.lean, line 72
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem map_inv_eq_ringInverse_map [FunLike F G₀ M₀]
    [MonoidWithZeroHomClass F G₀ M₀] (f : F) (a : G₀) :
    f a⁻¹ = (f a)⁻¹ʳ := by
  rcases subsingleton_or_nontrivial M₀ with h | h
  · exact Subsingleton.elim _ _
  · rw [← Ring.inverse_eq_inv a]
    exact map_ringInverse f a
