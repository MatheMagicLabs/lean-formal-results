/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.le_sum_log_nat
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Log/Sum.lean, line 92
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem le_sum_log_nat : N * log N - N ≤ ∑ n ∈ Ioc 0 N, log n := by
  rw [sum_log_eq_log_factorial]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have h := Real.pow_div_factorial_le_exp (N:ℝ) (Nat.cast_nonneg N) N
  have hf : (0:ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  rw [div_le_iff₀ hf] at h
  have h2 := Real.log_le_log (pow_pos hNr N) h
  rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp] at h2
  linarith
