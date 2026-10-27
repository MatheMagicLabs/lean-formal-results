/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.sum_log_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Log/Sum.lean, line 49
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem sum_log_le (hx : 1 ≤ x) : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * log x - x + log x + 1 := by
  have hx0 : 0 < x := by linarith
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  obtain ⟨M, hM⟩ : ∃ M, ⌊x⌋₊ = M + 1 := ⟨⌊x⌋₊ - 1, by omega⟩
  rw [hM] at hNx
  push_cast at hNx
  rw [sum_log_eq_log_factorial, ← sum_log_add_one_eq_log_factorial, hM, sum_range_succ]
  have hmono : MonotoneOn log (Set.Icc (1:ℝ) (1 + M)) :=
    strictMonoOn_log.monotoneOn.mono (fun t ht => by show (0:ℝ) < t; linarith [ht.1])
  have hs := hmono.sum_le_integral
  rw [integral_log] at hs
  simp only [log_one, mul_zero, sub_zero, add_comm (1:ℝ)] at hs
  have hy0 : (0:ℝ) < M + 1 := by positivity
  have hly : 0 ≤ log ((M:ℝ) + 1) :=
    log_nonneg (by linarith [(M.cast_nonneg : (0:ℝ) ≤ M)])
  have hlyx : log ((M:ℝ) + 1) ≤ log x := log_le_log hy0 hNx
  have h1 : log (((M:ℝ) + 1) / x) ≤ ((M:ℝ) + 1) / x - 1 :=
    log_le_sub_one_of_pos (div_pos hy0 hx0)
  rw [log_div hy0.ne' hx0.ne'] at h1
  have h2 : x * (((M:ℝ) + 1) / x - 1) = (M:ℝ) + 1 - x := by
    field_simp <;> ring
  have h3 := mul_le_mul_of_nonneg_left h1 hx0.le
  rw [h2] at h3
  have h4 : 0 ≤ (x - ((M:ℝ) + 1)) * log ((M:ℝ) + 1) := mul_nonneg (by linarith) hly
  nlinarith
