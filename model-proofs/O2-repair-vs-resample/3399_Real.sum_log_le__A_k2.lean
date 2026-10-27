/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.sum_log_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Log/Sum.lean, line 49
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem sum_log_le (hx : 1 ≤ x) : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * log x - x + log x + 1 := by
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  set N := ⌊x⌋₊ with hN
  have hN1' : (1:ℝ) ≤ N := by exact_mod_cast hN1
  have hmono : ∀ a b : ℝ, 1 ≤ a → a ≤ b → MonotoneOn log (Set.Icc a b) :=
    fun a b ha _ u hu v _ huv => log_le_log (by linarith [hu.1]) huv
  have hset : Ioc 0 N = Ico 1 (N+1) := by
    ext; simp; omega
  rw [hset, sum_Ico_succ_top hN1]
  have h2 : ∑ i ∈ Ico 1 N, log (i:ℝ) ≤ ∫ t in ((1:ℕ):ℝ)..N, log t :=
    MonotoneOn.sum_le_integral_Ico hN1 (hmono _ _ (by simp) (by exact_mod_cast hN1))
  rw [Nat.cast_one] at h2
  have hi1 : IntervalIntegrable log volume 1 (N:ℝ) :=
    MonotoneOn.intervalIntegrable (by rw [Set.uIcc_of_le hN1']; exact hmono _ _ le_rfl hN1')
  have hi2 : IntervalIntegrable log volume (N:ℝ) x :=
    MonotoneOn.intervalIntegrable (by rw [Set.uIcc_of_le hNx]; exact hmono _ _ hN1' hNx)
  have hadd := integral_add_adjacent_intervals hi1 hi2
  have hnn : 0 ≤ ∫ t in (N:ℝ)..x, log t :=
    integral_nonneg hNx (fun u hu => log_nonneg (by linarith [hu.1]))
  have h3 : ∫ t in (1:ℝ)..x, log t = x * log x - 1 * log 1 - x + 1 := by
    rw [integral_log]
    all_goals (try (rw [Set.mem_uIcc]; push_neg; constructor <;> intro h <;> linarith))
  have h4 : log (N:ℝ) ≤ log x := log_le_log (by linarith) hNx
  rw [log_one] at h3
  linarith
