/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ProbabilityTheory.minimaxRisk_compProd_le_minimaxRisk
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Decision/Risk/Basic.lean, line 283
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma minimaxRisk_compProd_le_minimaxRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    [IsSFiniteKernel P] (η : Kernel (Θ × 𝓧) 𝓧') [IsMarkovKernel η] :
    minimaxRisk ℓ (P ⊗ₖ η) ≤ minimaxRisk ℓ P := by
  have : P = (Kernel.deterministic Prod.fst (by fun_prop)) ∘ₖ (P ⊗ₖ η) := by
    rw [Kernel.deterministic_comp_eq_map, ← Kernel.fst_eq, Kernel.fst_compProd]
  nth_rw 2 [this]
  exact minimaxRisk_le_minimaxRisk_comp _ _ _
