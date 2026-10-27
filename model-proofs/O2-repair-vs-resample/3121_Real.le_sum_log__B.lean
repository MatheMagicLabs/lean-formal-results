/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.le_sum_log
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Log/Sum.lean, line 67
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem le_sum_log (hx : 1 ≤ x) : x * log x - x - log x + 1 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n := by
  have hx0 : 0 < x := by linarith
  have aux1 : (⌊x⌋₊ : ℝ) ≤ x := floor_le hx0.le
  have aux2 : 1 ≤ ⌊x⌋₊ := by simpa
  have aux3 : x < ⌊x⌋₊ + 1 := lt_floor_add_one x
  have hM1 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast aux2
  have hM : (0 : ℝ) < ⌊x⌋₊ := by linarith
  have h := (strictMonoOn_log.monotoneOn.mono
    (fun t ht => lt_of_lt_of_le one_pos (by simpa using ht.1) :
      Set.Icc (((1 : ℕ) : ℝ)) ((⌊x⌋₊ : ℕ) : ℝ) ⊆ Set.Ioi 0)).integral_le_sum_Ico aux2
  have hset : Ioc 0 ⌊x⌋₊ = Ico 1 (⌊x⌋₊ + 1) := by
    ext n; simp; omega
  have hsh := Finset.sum_Ico_add' (fun n : ℕ => log (n : ℝ)) 1 ⌊x⌋₊ 1
  have hsum : ∑ n ∈ Ioc 0 ⌊x⌋₊, log (n : ℝ)
      = ∑ i ∈ Ico 1 ⌊x⌋₊, log (((i + 1 : ℕ)) : ℝ) := by
    rw [hsh, hset, sum_eq_sum_Ico_succ_bot (by omega)]
    simp
  have hI : ∫ t in ((1 : ℕ) : ℝ)..((⌊x⌋₊ : ℕ) : ℝ), log t
      = (⌊x⌋₊ : ℝ) * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by
    rw [integral_log, Nat.cast_one, log_one]; ring
  have hlog := log_le_sub_one_of_pos (div_pos hx0 hM)
  rw [log_div hx0.ne' hM.ne'] at hlog
  have hdiv : (⌊x⌋₊ : ℝ) * (x / ⌊x⌋₊) = x := by field_simp
  have hp := mul_le_mul_of_nonneg_left hlog hM.le
  have hq := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - (x - ⌊x⌋₊)) (log_nonneg hx)
  rw [hsum]
  nlinarith [h, hI, hp, hq, hdiv]
