/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ProbabilityTheory.nullSingletonClass_gaussianReal
Source:      Mathlib @ d0a050ad6, Mathlib/Probability/Distributions/Gaussian/Real.lean, line 235 (group STABLE)
Experiment:  D1-deepseek-16-samples, arm sample 6, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 16 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
lemma nullSingletonClass_gaussianReal {μ : ℝ} {v : ℝ≥0} (h : v ≠ 0) :
    NullSingletonClass (gaussianReal μ v) := by
  rw [gaussianReal_of_var_ne_zero _ h]
  apply nullSingletonClass_withDensity
  <;> simp [gaussianPDF_pos, h]
  <;> apply Measurable.ennreal_ofReal
  <;> fun_prop
