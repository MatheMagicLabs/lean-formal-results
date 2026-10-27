/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     LaurentPolynomial.support_coeff_C_mul_T_of_ne_zero
Source:      Mathlib @ d0a050ad6, Mathlib/Algebra/Polynomial/Laurent.lean, line 378 (group DRIFT)
Experiment:  D1-deepseek-16-samples, arm sample 0, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 16 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
theorem support_coeff_C_mul_T_of_ne_zero {a : R} (a0 : a ≠ 0) (n : ℤ) :
    (C a * T n).coeff.support = {n} := by
  rw [← single_eq_C_mul_T]
  exact support_single_ne_zero _ a0
