/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsUnit.map_ringInverse
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Units/Lemmas.lean, line 30
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
protected theorem IsUnit.map_ringInverse [MonoidHomClass F M₀ M₀'] (f : F) {a : M₀} (h : IsUnit a) :
    f a⁻¹ʳ = (f a)⁻¹ʳ := by
  obtain ⟨u, rfl⟩ := h
  have h2 : f (u : M₀) = ((Units.map (f : M₀ →* M₀') u : M₀'ˣ) : M₀') := rfl
  rw [Ring.inverse_unit, h2, Ring.inverse_unit]
  first
    | rfl
    | simp
