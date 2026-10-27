/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MvPowerSeries.optionEquivLeft_X_none
Source:      Mathlib @ d0a050ad6, Mathlib/RingTheory/MvPowerSeries/Equiv.lean, line 148 (group DRIFT)
Experiment:  UE1-deepseek-8-samples, arm sample 7, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
lemma optionEquivLeft_X_none : optionEquivLeft σ R (X none) = PowerSeries.X := by
  simpa [← X_def, PowerSeries.monomial_eq_C_mul_X_pow] using
    optionEquivLeft_monomial (single none 1 : Option σ →₀ ℕ) (1 : R)
