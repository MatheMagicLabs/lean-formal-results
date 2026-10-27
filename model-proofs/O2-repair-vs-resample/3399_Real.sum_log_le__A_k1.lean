/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.sum_log_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Log/Sum.lean, line 49
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem sum_log_le (hx : 1 ≤ x) : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * log x - x + log x + 1 := by
  have key : ∀ N : ℕ, 1 ≤ N → log (N.factorial : ℝ) ≤ N * log N - N + log N + 1 := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [Nat.factorial_succ, Nat.cast_mul, log_mul (by positivity) (by positivity)]
      have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
      have hn0 : (n:ℝ) ≠ 0 := by positivity
      have hnpos : (0:ℝ) < n := by linarith
      have h1 := one_sub_inv_le_log_of_pos (x := ((n:ℝ)+1)/n) (div_pos (by positivity) hnpos)
      rw [log_div (by positivity) hn0] at h1
      have h2 : 1 - (((n:ℝ)+1)/n)⁻¹ = 1/(n+1) := by
        field_simp <;> ring
      rw [h2] at h1
      push_cast
      have h3 : 1 ≤ ((n:ℝ)+1) * (log (n+1) - log n) := by
        have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ n+1)
        rwa [mul_one_div_cancel (by positivity)] at this
      nlinarith
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hN : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  rw [sum_log_eq_log_factorial]
  have k := key _ hN
  have hy1 : (1:ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN
  have hypos : (0:ℝ) < ⌊x⌋₊ := by linarith
  have hlog : log (⌊x⌋₊ : ℝ) ≤ log x := log_le_log hypos hNx
  have hly : 0 ≤ log (⌊x⌋₊ : ℝ) := log_nonneg hy1
  have h1 := one_sub_inv_le_log_of_pos (x := x / ⌊x⌋₊) (div_pos hxpos hypos)
  rw [log_div hxpos.ne' hypos.ne'] at h1
  have h2 : x - ⌊x⌋₊ ≤ x * (log x - log ⌊x⌋₊) := by
    have := mul_le_mul_of_nonneg_left h1 hx0
    have e : x * (1 - (x / ⌊x⌋₊)⁻¹) = x - ⌊x⌋₊ := by
      have := hxpos.ne'
      have := hypos.ne'
      field_simp <;> ring
    linarith
  have h3 := mul_nonneg (sub_nonneg.2 hNx) hly
  nlinarith
