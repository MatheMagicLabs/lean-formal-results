/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsUnit.map_ringInverse
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Units/Lemmas.lean, line 30
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
protected theorem IsUnit.map_ringInverse [MonoidHomClass F M₀ M₀'] (f : F) {a : M₀} (h : IsUnit a) :
    f a⁻¹ʳ = (f a)⁻¹ʳ := by
  obtain ⟨u, rfl⟩ := h
  rw [Ring.inverse_unit]
  have : (f (u : M₀)) = ((Units.map (f : M₀ →* M₀') u : M₀'ˣ) : M₀') := rfl
  rw [this, Ring.inverse_unit]
  rfl
