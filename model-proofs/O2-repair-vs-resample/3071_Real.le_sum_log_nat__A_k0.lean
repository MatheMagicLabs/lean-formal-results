/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.le_sum_log_nat
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Log/Sum.lean, line 92
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem le_sum_log_nat : N * log N - N ≤ ∑ n ∈ Ioc 0 N, log n := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · rw [sum_log_eq_log_factorial]
    have h := Real.pow_div_factorial_le_exp (x := (N:ℝ)) (by positivity) N
    have hf : (0:ℝ) < (Nat.factorial N : ℝ) := by exact_mod_cast Nat.factorial_pos N
    rw [div_le_iff₀ hf] at h
    have hN' : (0:ℝ) < N := by exact_mod_cast hN
    have := log_le_log (by positivity) h
    rw [log_pow, log_mul (exp_pos _).ne' hf.ne', log_exp] at this
    linarith
