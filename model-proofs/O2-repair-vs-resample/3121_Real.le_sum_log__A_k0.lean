/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.le_sum_log
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Log/Sum.lean, line 67
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem le_sum_log (hx : 1 ≤ x) : x * log x - x - log x + 1 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n := by
  have aux1 : (⌊x⌋₊ : ℝ) ≤ x := floor_le (by linarith)
  have aux2 : 1 ≤ ⌊x⌋₊ := by simpa
  have aux3 : x < ⌊x⌋₊ + 1 := lt_floor_add_one x
  have hM : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast aux2
  have h1 : (∫ t in (1 : ℕ)..⌊x⌋₊, log t) ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n := by
    calc _ ≤ ∑ n ∈ Ico 1 ⌊x⌋₊, log ((n + 1 : ℕ) : ℝ) :=
          (strictMonoOn_log.monotoneOn.mono (by grind)).integral_le_sum_Ico aux2
      _ = ∑ n ∈ Ico (1 + 1) (⌊x⌋₊ + 1), log (n : ℝ) :=
          sum_Ico_add' (fun n : ℕ => log (n : ℝ)) 1 ⌊x⌋₊ 1
      _ ≤ _ := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro n hn
            simp at hn ⊢
            omega
          · intro n _ _
            exact log_natCast_nonneg n
  have hI : (∫ t in (1 : ℕ)..⌊x⌋₊, log t) = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by
    rw [integral_log]
    simp
  have h2 : log x - log ⌊x⌋₊ ≤ x / ⌊x⌋₊ - 1 := by
    rw [← log_div (by linarith) hM.ne']
    exact log_le_sub_one_of_pos (by positivity)
  have h3 : (⌊x⌋₊ : ℝ) * (x / ⌊x⌋₊) = x := mul_div_cancel₀ _ hM.ne'
  have h4 : (x - ⌊x⌋₊) * log x ≤ log x :=
    mul_le_of_le_one_left (log_nonneg hx) (by linarith)
  have h5 := mul_le_mul_of_nonneg_left h2 hM.le
  linarith
