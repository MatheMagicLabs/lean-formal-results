/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ProbabilityTheory.minimaxRisk_le_minimaxRisk_comp
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Decision/Risk/Basic.lean, line 265
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma minimaxRisk_le_minimaxRisk_comp (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    (η : Kernel 𝓧 𝓧') [IsMarkovKernel η] :
    minimaxRisk ℓ P ≤ minimaxRisk ℓ (η ∘ₖ P) := by
  simp only [minimaxRisk, le_iInf_iff]
  intro κ hκ
  refine iInf_le_of_le (κ ∘ₖ η) (iInf_le_of_le inferInstance ?_)
  simp only [Kernel.comp_assoc, le_refl]
