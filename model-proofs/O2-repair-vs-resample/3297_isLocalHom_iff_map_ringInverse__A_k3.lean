/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     isLocalHom_iff_map_ringInverse
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Units/Lemmas.lean, line 44
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem isLocalHom_iff_map_ringInverse [MonoidWithZeroHomClass F M₀ M₀'] [Nontrivial M₀'] (f : F) :
    IsLocalHom f ↔ ∀ a, f a⁻¹ʳ = (f a)⁻¹ʳ := by
  constructor
  · intro _ a
    exact map_ringInverse f a
  · intro h
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 := Ring.mul_inverse_cancel (f a) ha
    rw [← h a, Ring.inverse_non_unit _ hna, map_zero, mul_zero] at h1
    exact zero_ne_one h1
