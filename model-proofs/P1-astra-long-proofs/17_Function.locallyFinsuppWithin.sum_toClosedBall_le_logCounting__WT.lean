/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Function.locallyFinsuppWithin.sum_toClosedBall_le_logCounting
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Basic.lean, line 254
             (added after the model's training data; human proof 61 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 3 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem sum_toClosedBall_le_logCounting {D : Function.locallyFinsupp ℂ ℤ} {ρ r : ℝ}
    (hD : 0 ≤ D) (hρ : 1 ≤ ρ) (hρr : ρ < r) :
    (∑ᶠ z, (D.toClosedBall ρ z : ℝ)) * Real.log (r / ρ) ≤ D.logCounting r := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hrpos : 0 < r := hρpos.trans hρr
  have hr : 1 ≤ r := hρ.trans hρr.le
  have hsub : closedBall (0 : ℂ) |ρ| ⊆ closedBall 0 |r| := closedBall_subset_closedBall (by simpa [abs_of_pos hρpos, abs_of_pos hrpos] using hρr.le)
  have hlog : ∀ (a : ℝ), 1 ≤ a → ∀ z : ℂ, z ∈ closedBall 0 |a| → log ‖z‖ ≤ log a := by
    intro a ha z hz
    have hap : 0 < a := lt_of_lt_of_le zero_lt_one ha
    have hza : ‖z‖ ≤ a := by simpa [mem_closedBall, dist_zero_right, abs_of_pos hap] using hz
    by_cases hz0 : z = 0
    · simpa [hz0] using log_nonneg ha
    · exact log_le_log (norm_pos_iff.mpr hz0) hza
  have hzero : D.toClosedBall r 0 = D 0 := toClosedBall_eval_within D (by simp)
  have heq : D.logCounting r = ∑ᶠ z, (D.toClosedBall r z : ℝ) * (log r - log ‖z‖) := by
    simpa only [logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk, zero_sub, norm_neg, hzero] using (countingFunction_finsum_eq_finsum_add (c := 0) (R := r) (D := fun z ↦ D.toClosedBall r z) hrpos.ne' ((D.toClosedBall r).finiteSupport (isCompact_closedBall 0 |r|))).symm
  rw [heq, finsum_mul]
  refine finsum_le_finsum ?_ ?_ ?_
  · exact ((D.toClosedBall ρ).finiteSupport (isCompact_closedBall 0 |ρ|)).subset (fun _ _ ↦ by simp_all)
  · exact ((D.toClosedBall r).finiteSupport (isCompact_closedBall 0 |r|)).subset (fun _ _ ↦ by simp_all)
  · intro z
    change (D.toClosedBall ρ z : ℝ) * log (r / ρ) ≤ (D.toClosedBall r z : ℝ) * (log r - log ‖z‖)
    by_cases hzρ : z ∈ closedBall 0 |ρ|
    · rw [toClosedBall_eval_within D hzρ, toClosedBall_eval_within D (hsub hzρ), log_div hrpos.ne' hρpos.ne']
      exact mul_le_mul_of_nonneg_left (sub_le_sub_left (hlog ρ hρ z hzρ) (log r)) (Int.cast_nonneg (hD z))
    · rw [apply_eq_zero_of_notMem (D.toClosedBall ρ) hzρ]
      simp only [Int.cast_zero, zero_mul]
      by_cases hzr : z ∈ closedBall 0 |r|
      · rw [toClosedBall_eval_within D hzr]
        exact mul_nonneg (Int.cast_nonneg (hD z)) (sub_nonneg.mpr (hlog r hr z hzr))
      · simp [apply_eq_zero_of_notMem (D.toClosedBall r) hzr]
