/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ProbabilityTheory.integral_geometricMeasure
Source:      Mathlib @ d0a050ad6, Mathlib/Probability/Distributions/Geometric.lean, line 137 (group DRIFT)
Experiment:  UE1-deepseek-8-samples, arm sample 3, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
lemma integral_geometricMeasure [FiniteDimensional ℝ E] (hp : p ≠ 0) (f : ℕ → E) :
    ∫ n, f n ∂geometricMeasure p = ∑' n : ℕ, ((1 - p : ℝ) ^ n * p) • f n := by
  have h1 : (fun n ↦ ((1 - p : ℝ) ^ n * p) • f n) = fun n ↦ (ENNReal.ofReal ((1 - p) ^ n * p)).toReal • f n := by
    ext n; rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]
  rw [h1, geometricMeasure_eq hp, integral_sum_dirac (by simp)]
  <;> simp [geometricMeasure_nonneg]
  <;> congr 1
  <;> ext n
  <;> simp [geometricMeasure_nonneg]
  <;> congr 1
  <;> ring
