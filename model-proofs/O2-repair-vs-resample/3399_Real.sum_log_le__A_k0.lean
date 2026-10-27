/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.sum_log_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Log/Sum.lean, line 49
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem sum_log_le (hx : 1 ≤ x) : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * log x - x + log x + 1 := by
  have hx0 : (0:ℝ) < x := by linarith
  obtain ⟨N, hN⟩ : ∃ N, ⌊x⌋₊ = N := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by rw [← hN]; exact Nat.le_floor (by exact_mod_cast hx)
  have hNx : (N:ℝ) ≤ x := by rw [← hN]; exact Nat.floor_le hx0.le
  rw [hN]
  have hN1' : (1:ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0:ℝ) < N := by linarith
  have hsplit : Ioc 0 N = Ico 1 (N+1) := by
    ext a
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [hsplit, sum_Ico_succ_top (by omega)]
  have hmono : MonotoneOn Real.log (Set.Icc ((1:ℕ):ℝ) (N:ℝ)) := by
    intro a ha b hb hab
    simp only [Set.mem_Icc, Nat.cast_one] at ha hb
    exact log_le_log (by linarith) hab
  have h2 := hmono.sum_le_integral_Ico hN1
  have h3 : ∫ t in (1:ℝ)..N, log t = N * log N - N + 1 := by
    rw [integral_log]
    · simp
      try ring
    all_goals
      rw [Set.mem_uIcc]
      intro h
      rcases h with h | h <;> linarith [h.1, h.2]
  rw [Nat.cast_one, h3] at h2
  have hlog : log (N/x) ≤ N/x - 1 := log_le_sub_one_of_pos (div_pos hNpos hx0)
  rw [log_div hNpos.ne' hx0.ne'] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog hx0.le
  have e : x * (N/x - 1) = N - x := by
    field_simp
    try ring
  rw [e] at hm
  have hlN : 0 ≤ log N := log_nonneg hN1'
  have hlx : log N ≤ log x := log_le_log hNpos hNx
  nlinarith [mul_nonneg (sub_nonneg.mpr hNx) hlN]
