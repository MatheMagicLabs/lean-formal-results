/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Complex.restrictScalars_toSpanSingleton
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/Complex/Basic.lean, line 197 (group STABLE)
Experiment:  D1-deepseek-16-samples, arm sample 10, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 16 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
theorem restrictScalars_toSpanSingleton (x : ℂ) :
    ContinuousLinearMap.restrictScalars ℝ (toSpanSingleton ℂ x : ℂ →L[ℂ] ℂ) =
    x • (1 : ℂ →L[ℝ] ℂ) := by
  ext1 z
  simp [smul_eq_mul, mul_add, add_mul, mul_comm, mul_left_comm]
  <;> ring_nf
  <;> simp [Complex.ext_iff]
  <;> aesop
