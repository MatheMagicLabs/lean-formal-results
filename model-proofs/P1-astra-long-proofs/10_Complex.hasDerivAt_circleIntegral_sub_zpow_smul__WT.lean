/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Complex.hasDerivAt_circleIntegral_sub_zpow_smul
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/Complex/CauchyIntegral.lean, line 587
             (added after the model's training data; human proof 30 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 5 call(s)
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
  obtain ⟨r, hr, hrs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (isClosed_sphere.isOpen_compl.mem_nhds hw)
  have hne : ∀ z ∈ sphere c |R|, ∀ x ∈ closedBall w r, z - x ≠ 0 := by intro z hz x hx; exact sub_ne_zero.mpr (ne_of_mem_of_not_mem hz (hrs hx))
  have hcont : ContinuousOn (fun p : ℂ × ℂ ↦ (-n : ℂ) * (p.1 - p.2) ^ (n - 1)) (sphere c |R| ×ˢ closedBall w r) := continuousOn_const.mul ((continuous_fst.sub continuous_snd).continuousOn.zpow₀ _ (fun p hp ↦ Or.inl (hne p.1 hp.1 p.2 hp.2)))
  obtain ⟨M, hM⟩ := (isCompact_sphere c |R| |>.prod (isCompact_closedBall w r)).exists_bound_of_continuousOn hcont
  let g : ℝ → E := fun t ↦ deriv (circleMap c R) t • f (circleMap c R t)
  have hg : IntervalIntegrable g volume 0 (2 * π) := hf.out
  have hi : ∀ x ∈ closedBall w r, ∀ m : ℤ, IntervalIntegrable (fun t ↦ (circleMap c R t - x) ^ m • g t) volume 0 (2 * π) := by intro x hx m; exact hg.continuousOn_smul (((continuous_circleMap c R).sub continuous_const).continuousOn.zpow₀ m (fun t _ ↦ Or.inl (hne _ (circleMap_mem_sphere' _ _ _) x hx)))
  have hwm : w ∈ closedBall w r := mem_closedBall_self hr.le
  have hdi : IntervalIntegrable (fun t ↦ ((-n : ℂ) * (circleMap c R t - w) ^ (n - 1)) • g t) volume 0 (2 * π) := hg.continuousOn_smul (continuousOn_const.mul (((continuous_circleMap c R).sub continuous_const).continuousOn.zpow₀ (n - 1) (fun t _ ↦ Or.inl (hne _ (circleMap_mem_sphere' _ _ _) w hwm))))
  have hmeas : AEStronglyMeasurable (fun t ↦ ((-n : ℂ) * (circleMap c R t - w) ^ (n - 1)) • g t) (volume.restrict (Ι (0 : ℝ) (2 * π))) := by simpa only [uIoc_of_le Real.two_pi_pos.le] using hdi.aestronglyMeasurable
  have h := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
  (F := fun x t ↦ (circleMap c R t - x) ^ n • g t)
  (F' := fun x t ↦ ((-n : ℂ) * (circleMap c R t - x) ^ (n - 1)) • g t)
  (bound := fun t ↦ M * ‖g t‖)
  (Metric.closedBall_mem_nhds w hr)
  (Filter.Eventually.mono (Metric.closedBall_mem_nhds w hr) (fun x hx ↦ by simpa only [uIoc_of_le Real.two_pi_pos.le] using (hi x hx n).aestronglyMeasurable))
  (hi w hwm n) hmeas
  (Filter.Eventually.of_forall (fun t _ x hx ↦ by rw [norm_smul]; exact mul_le_mul_of_nonneg_right (hM (circleMap c R t, x) ⟨circleMap_mem_sphere' _ _ _, hx⟩) (norm_nonneg _)))
  (hg.norm.const_mul M)
  (Filter.Eventually.of_forall (fun t _ x hx ↦ by simpa only [Function.comp_def, mul_neg_one, neg_mul] using ((hasDerivAt_zpow n (circleMap c R t - x) (Or.inl (hne _ (circleMap_mem_sphere' _ _ _) x hx))).comp x ((hasDerivAt_id x).const_sub (circleMap c R t))).smul_const (g t))))
  have heq : ∀ x : ℂ, ∀ m : ℤ, (∮ z in C(c, R), (z - x) ^ m • f z) = ∫ t in (0 : ℝ)..2 * π, (circleMap c R t - x) ^ m • g t := by intro x m; apply intervalIntegral.integral_congr; intro t _; exact smul_comm _ _ _
  simpa only [mul_smul, intervalIntegral.integral_smul, ← heq] using h.2
