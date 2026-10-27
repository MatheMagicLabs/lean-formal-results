/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.sum_log_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Log/Sum.lean, line 49
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem sum_log_le (hx : 1 ≤ x) : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * log x - x + log x + 1 := by
  have key : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Ioc 0 N, log n ≤ N * log N - N + log N + 1 := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simp [sum_log_eq_log_factorial]
    | succ N hN ih =>
      rw [sum_Ioc_succ_top (by omega)]
      have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
      have hpos : (0:ℝ) < N + 1 := by linarith
      have h1 := log_le_sub_one_of_pos (show 0 < (N:ℝ) / (N+1) from div_pos (by linarith) hpos)
      rw [log_div (ne_of_gt (by linarith)) hpos.ne'] at h1
      have h2 : (N:ℝ) / (N+1) * (N+1) = N := by field_simp
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left h1 hpos.le]
  have hx0 : (0:ℝ) < x := by linarith
  have hN : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hNx : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0.le
  set M := ⌊x⌋₊ with hM
  have hN1 : (1:ℝ) ≤ M := by exact_mod_cast hN
  have hk := key M hN
  have h1 := log_le_sub_one_of_pos (show 0 < (M:ℝ) / x from div_pos (by linarith) hx0)
  rw [log_div (ne_of_gt (by linarith)) hx0.ne'] at h1
  have h2 : (M:ℝ) / x * x = M := by field_simp
  have hlogN : 0 ≤ log (M:ℝ) := log_nonneg hN1
  have hlog : log (M:ℝ) ≤ log x := log_le_log (by linarith) hNx
  nlinarith [mul_le_mul_of_nonneg_left h1 hx0.le, mul_le_mul_of_nonneg_left hNx hlogN]
