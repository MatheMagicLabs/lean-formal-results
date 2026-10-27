/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ProbabilityTheory.minimaxRisk_le_minimaxRisk_map
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Decision/Risk/Basic.lean, line 275
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-haiku, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-haiku-4-5
Setup:       Haiku 4.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma minimaxRisk_le_minimaxRisk_map (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    {f : 𝓧 → 𝓧'} (hf : Measurable f) :
    minimaxRisk ℓ P ≤ minimaxRisk ℓ (P.map f) := by
  rw [← Kernel.deterministic_comp_eq_map hf]
  exact minimaxRisk_le_minimaxRisk_comp _ _ _
