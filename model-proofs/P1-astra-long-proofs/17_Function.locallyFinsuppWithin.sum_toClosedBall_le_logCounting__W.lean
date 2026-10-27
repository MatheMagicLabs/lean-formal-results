/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Function.locallyFinsuppWithin.sum_toClosedBall_le_logCounting
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Basic.lean, line 254
             (added after the model's training data; human proof 61 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 2 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem sum_toClosedBall_le_logCounting {D : Function.locallyFinsupp ℂ ℤ} {ρ r : ℝ}
    (hD : 0 ≤ D) (hρ : 1 ≤ ρ) (hρr : ρ < r) :
    (∑ᶠ z, (D.toClosedBall ρ z : ℝ)) * Real.log (r / ρ) ≤ D.logCounting r := by
  classical
  have hρ0 : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hr0 : 0 < r := hρ0.trans hρr
  have hs := (D.toClosedBall r).finiteSupport (isCompact_closedBall 0 |r|)
  let s := insert (0 : ℂ) hs.toFinset
  have hleft : (∑ᶠ z, (D.toClosedBall ρ z : ℝ)) = ∑ z ∈ s, (D.toClosedBall ρ z : ℝ) := by {
  apply finsum_eq_sum_of_support_subset
  intro z hz
  have hz' : D.toClosedBall ρ z ≠ 0 := by {
  intro h
  exact hz (by simp [h]) }
  have hzρ : z ∈ closedBall 0 |ρ| := toClosedBall_support_subset_closedBall D hz'
  have hzr : z ∈ closedBall 0 |r| := by {
  simp only [mem_closedBall, dist_zero_right, abs_of_pos hρ0] at hzρ
  simpa only [mem_closedBall, dist_zero_right, abs_of_pos hr0] using hzρ.trans hρr.le }
  have hz'' : D.toClosedBall r z ≠ 0 := by {
  rw [toClosedBall_eval_within _ hzr]
  rwa [toClosedBall_eval_within _ hzρ] at hz' }
  exact Finset.mem_insert_of_mem (hs.mem_toFinset.mpr hz'') }
  have hright : (∑ᶠ z, (D.toClosedBall r z : ℝ) * log (r * ‖z‖⁻¹)) =
  ∑ z ∈ s, (D.toClosedBall r z : ℝ) * log (r * ‖z‖⁻¹) := by {
  apply finsum_eq_sum_of_support_subset
  intro z hz
  have hz' : D.toClosedBall r z ≠ 0 := by {
  intro h
  exact hz (by simp [h]) }
  exact Finset.mem_insert_of_mem (hs.mem_toFinset.mpr hz') }
  change (∑ᶠ z, (D.toClosedBall ρ z : ℝ)) * log (r / ρ) ≤
  (∑ᶠ z, (D.toClosedBall r z : ℝ) * log (r * ‖z‖⁻¹)) + (D 0 : ℝ) * log r
  rw [hleft, hright, Finset.sum_mul]
  have hlog : log (r / ρ) ≤ log r := by {
  rw [log_div (ne_of_gt hr0) (ne_of_gt hρ0)]
  exact sub_le_self _ (log_nonneg hρ) }
  have hsum :
  (∑ z ∈ s, (D.toClosedBall ρ z : ℝ) * log (r / ρ)) ≤
  ∑ z ∈ s, ((D.toClosedBall r z : ℝ) * log (r * ‖z‖⁻¹) +
  if z = 0 then (D 0 : ℝ) * log r else 0) := by {
  apply Finset.sum_le_sum
  intro z hz
  have hzr : z ∈ closedBall 0 |r| := by {
  rcases Finset.mem_insert.mp hz with hz | hz
  · { subst z; simp }
  · { exact toClosedBall_support_subset_closedBall D (hs.mem_toFinset.mp hz) } }
  by_cases hz0 : z = 0
  · {
  subst z
  simpa [toClosedBall_eval_within D (show (0 : ℂ) ∈ closedBall 0 |ρ| by simp)] using
  mul_le_mul_of_nonneg_left hlog (Int.cast_nonneg (hD 0)) }
  · {
  rw [if_neg hz0, add_zero, toClosedBall_eval_within _ hzr]
  by_cases hzρ : z ∈ closedBall 0 |ρ|
  · {
  rw [toClosedBall_eval_within _ hzρ]
  apply mul_le_mul_of_nonneg_left _ (Int.cast_nonneg (hD z))
  apply Real.log_le_log (div_pos hr0 hρ0)
  rw [← div_eq_mul_inv]
  apply (div_le_div_iff₀ hρ0 (norm_pos_iff.mpr hz0)).2
  have hn : ‖z‖ ≤ ρ := by simpa [mem_closedBall, dist_zero_right, abs_of_pos hρ0] using hzρ
  exact mul_le_mul_of_nonneg_left hn hr0.le }
  · {
  rw [apply_eq_zero_of_notMem _ hzρ, Int.cast_zero, zero_mul]
  apply mul_nonneg (Int.cast_nonneg (hD z))
  apply log_nonneg
  apply (le_mul_inv_iff₀ (norm_pos_iff.mpr hz0)).2
  simpa [mem_closedBall, dist_zero_right, abs_of_pos hr0] using hzr } } }
  simpa [Finset.sum_add_distrib, s] using hsum
