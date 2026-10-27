/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.le_sum_log
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Log/Sum.lean, line 67
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem le_sum_log (hx : 1 ≤ x) : x * log x - x - log x + 1 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n := by
  have aux1 : (⌊x⌋₊ : ℝ) ≤ x := floor_le (by linarith)
  have aux2 : 1 ≤ ⌊x⌋₊ := by simpa
  have hN : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast aux2
  have h1 : ∫ t in (1 : ℝ)..(⌊x⌋₊ : ℝ), log t ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n := by
    have := (strictMonoOn_log.monotoneOn.mono (by grind)).integral_le_sum_Ico aux2
    rw [Nat.cast_one] at this
    refine this.trans ?_
    rw [sum_log_eq_log_factorial, ← sum_log_add_one_eq_log_factorial]
    calc ∑ i ∈ Ico 1 ⌊x⌋₊, log (((i + 1 : ℕ)) : ℝ)
        ≤ ∑ i ∈ range ⌊x⌋₊, log (((i + 1 : ℕ)) : ℝ) :=
          sum_le_sum_of_subset_of_nonneg
            (by intro i hi; rw [mem_Ico] at hi; rw [mem_range]; exact hi.2)
            (fun i _ _ => log_nonneg (by exact_mod_cast Nat.le_add_left 1 i))
      _ = _ := by simp
  have hI : ∫ t in (1 : ℝ)..(⌊x⌋₊ : ℝ), log t
      = (⌊x⌋₊ : ℝ) * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by
    rw [integral_log, log_one]; ring
  have hd : log x - log ⌊x⌋₊ ≤ x / ⌊x⌋₊ - 1 := by
    rw [← log_div (by linarith) hN.ne']
    exact log_le_sub_one_of_pos (by positivity)
  have hmul : (⌊x⌋₊ : ℝ) * (x / ⌊x⌋₊ - 1) = x - ⌊x⌋₊ := by
    field_simp
  have hd' : (⌊x⌋₊ : ℝ) * (log x - log ⌊x⌋₊) ≤ x - ⌊x⌋₊ := by
    have := mul_le_mul_of_nonneg_left hd hN.le
    linarith
  have hlx : 0 ≤ log x := log_nonneg hx
  have hfl : x < ⌊x⌋₊ + 1 := lt_floor_add_one x
  have h3 : (x - ⌊x⌋₊) * log x ≤ log x := by
    have : 0 ≤ (1 - (x - ⌊x⌋₊)) * log x := mul_nonneg (by linarith) hlx
    linarith
  nlinarith [h1, hI, hd', h3]
