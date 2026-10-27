/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Complex.hasDerivAt_circleIntegral_sub_zpow_smul
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/Complex/CauchyIntegral.lean, line 587
             (added after the model's training data; human proof 30 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 4 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem hasDerivAt_circleIntegral_sub_zpow_smul {f : ℂ → E} {R : ℝ} {c w : ℂ} {n : ℤ}
    (hf : CircleIntegrable f c R) (hw : w ∉ sphere c |R|) :
    HasDerivAt (fun w ↦ ∮ z in C(c, R), (z - w) ^ n • f z)
      ((-n : ℂ) • ∮ z in C(c, R), (z - w) ^ (n - 1) • f z) w := by
  obtain ⟨d, hd, hdist⟩ := exists_ball_forall_le_norm_circleMap_sub hw
  have hfm : AEStronglyMeasurable (fun θ ↦ f (circleMap c R θ)) (volume.restrict (uIoc 0 (2 * π))) := (intervalIntegrable_iff.1 hf).aestronglyMeasurable
  simp only [circleIntegral, deriv_circleMap]
  rw [← intervalIntegral.integral_smul]
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (F' := fun x θ ↦ (-n : ℂ) • ((circleMap 0 R θ * I) • (circleMap c R θ - x) ^ (n - 1) • f (circleMap c R θ))) (bound := fun θ ↦ |(n : ℝ)| * |R| * max (d ^ (n - 1)) ((|R| + dist c w + d) ^ (n - 1)) * ‖f (circleMap c R θ)‖) (ball_mem_nhds w hd) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards with x; exact (Continuous.aestronglyMeasurable (by fun_prop)).smul ((Measurable.aestronglyMeasurable (by fun_prop)).smul hfm)
  · simpa only [deriv_circleMap] using (hf.sub_zpow_smul n hw).out
  · exact ((Continuous.aestronglyMeasurable (by fun_prop)).smul ((Measurable.aestronglyMeasurable (by fun_prop)).smul hfm)).const_smul _
  · filter_upwards with θ _ x hx; have hlb := hdist x hx θ; have hub : ‖circleMap c R θ - x‖ ≤ |R| + dist c w + d := (by have := mem_ball.1 hx; linarith [norm_circleMap_sub_le c R θ x, dist_triangle_right c x w]); have key : ‖circleMap c R θ - x‖ ^ (n - 1) ≤ max (d ^ (n - 1)) ((|R| + dist c w + d) ^ (n - 1)) := (by by_cases h : 0 ≤ n - 1; exact le_max_of_le_right (zpow_le_zpow_left₀ h (norm_nonneg _) hub); refine le_max_of_le_left ?_; rw [show n - 1 = -(1 - n) by ring, zpow_neg, zpow_neg]; exact inv_anti₀ (zpow_pos hd _) (zpow_le_zpow_left₀ (by omega) hd.le hlb)); have norm_eq : ‖(-n : ℂ) • ((circleMap 0 R θ * I) • (circleMap c R θ - x) ^ (n - 1) • f (circleMap c R θ))‖ = |(n : ℝ)| * |R| * ‖circleMap c R θ - x‖ ^ (n - 1) * ‖f (circleMap c R θ)‖ := (by rw [norm_smul, norm_smul, norm_smul, norm_neg, Complex.norm_intCast, norm_zpow, norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero]; ring); rw [norm_eq]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key (by positivity)) (norm_nonneg _)
  · exact (IntervalIntegrable.norm hf).const_mul _
  · filter_upwards with θ _ x hx; have hne : circleMap c R θ - x ≠ 0 := norm_pos_iff.mp (hd.trans_le (hdist x hx θ)); have h₁ : HasDerivAt (fun y : ℂ ↦ (circleMap c R θ - y) ^ n) (-((n : ℂ) * (circleMap c R θ - x) ^ (n - 1))) x := (hasDerivAt_zpow n _ (Or.inl hne)).comp_const_sub (circleMap c R θ) x; exact ((h₁.smul_const (f (circleMap c R θ))).const_smul (circleMap 0 R θ * I)).congr_deriv (by module)
