/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.volume_closedEBall
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean, line 156 (group DRIFT)
Experiment:  D1-deepseek-16-samples, arm sample 13, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 16 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
theorem volume_closedEBall (a : ℝ) (r : ℝ≥0∞) : volume (Metric.closedEBall a r) = 2 * r := by
  rcases eq_or_ne r ∞ with (rfl | hr)
  · rw [Metric.closedEBall_top, volume_univ, two_mul, _root_.top_add]
  · lift r to ℝ≥0 using hr
    rw [Metric.closedEBall_coe, volume_closedBall, two_mul, ← NNReal.coe_add, ENNReal.ofReal_coe_nnreal,
      ENNReal.coe_add, two_mul]
