/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.le_sum_log_nat
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Log/Sum.lean, line 92
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem le_sum_log_nat : N * log N - N ≤ ∑ n ∈ Ioc 0 N, log n := by
  rcases N.eq_zero_or_pos with rfl | hN
  · simp
  rw [sum_log_eq_log_factorial]
  have h := Real.pow_div_factorial_le_exp (N : ℝ) (by positivity) N
  have hpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hf : 0 < (N.factorial : ℝ) := by exact_mod_cast N.factorial_pos
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_div (by positivity) hf.ne', Real.log_pow, Real.log_exp] at h2
  linarith
