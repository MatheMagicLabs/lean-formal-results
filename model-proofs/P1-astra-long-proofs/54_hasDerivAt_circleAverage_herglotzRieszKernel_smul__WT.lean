/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     hasDerivAt_circleAverage_herglotzRieszKernel_smul
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/Complex/Poisson.lean, line 302
             (added after the model's training data; human proof 30 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 4 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem hasDerivAt_circleAverage_herglotzRieszKernel_smul (hg : CircleIntegrable f 0 R)
    (hw : w ∉ sphere 0 |R|) :
    HasDerivAt (fun w ↦ circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • f ζ) 0 R)
      (circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • f ζ) 0 R) w := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (isClosed_sphere.isOpen_compl.mem_nhds hw)
  have hhalf : 0 < r / 2 := by positivity
  have hout : ∀ x ∈ ball w (r / 2), x ∉ sphere 0 |R| := by {
  intro x hx
  apply hball
  exact mem_ball.mpr (lt_trans (mem_ball.mp hx) (by linarith)) }
  have hlower : ∀ x ∈ ball w (r / 2), ∀ ζ ∈ sphere 0 |R|, r / 2 ≤ ‖ζ - x‖ := by {
  intro x hx ζ hζ
  have hdist : r ≤ dist ζ w := by {
  by_contra! h
  exact hball (mem_ball.mpr h) hζ }
  have htri : dist ζ w ≤ ‖ζ - x‖ + dist x w := by {
  simpa only [dist_eq_norm] using dist_triangle ζ x w }
  have hx' : dist x w < r / 2 := mem_ball.mp hx
  linarith }
  have hne : ∀ x ∈ ball w (r / 2), ∀ ζ ∈ sphere 0 |R|, ζ - x ≠ 0 := by {
  intro x hx ζ hζ h
  have := hlower x hx ζ hζ
  rw [h, norm_zero] at this
  linarith }
  have hwball : w ∈ ball w (r / 2) := mem_ball_self hhalf
  have h_integrable : ∀ x ∈ ball w (r / 2), CircleIntegrable (fun ζ ↦ herglotzRieszKernel 0 x ζ • f ζ) 0 R := by {
  intro x hx
  exact hg.continuousOn_smul (continuousOn_herglotzRieszKernel_sphere (hout x hx)) }
  have hdint : CircleIntegrable (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • f ζ) 0 R := by {
  apply hg.continuousOn_smul
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro ζ hζ
  exact pow_ne_zero _ (hne w hwball ζ hζ) }
  have hder : ∀ x ∈ ball w (r / 2), ∀ ζ ∈ sphere 0 |R|, HasDerivAt (fun y ↦ herglotzRieszKernel 0 y ζ • f ζ) ((2 * ζ / (ζ - x) ^ 2) • f ζ) x := by {
  intro x hx ζ hζ
  have hk : HasDerivAt (fun y ↦ herglotzRieszKernel 0 y ζ) (2 * ζ / (ζ - x) ^ 2) x := by {
  convert ((hasDerivAt_const x ζ).add (hasDerivAt_id x)).fun_div ((hasDerivAt_const x ζ).sub (hasDerivAt_id x)) (hne x hx ζ hζ) using 1 <;> simp only [herglotzRieszKernel, sub_zero, Pi.add_apply, Pi.sub_apply, id_eq] <;> ring }
  exact hk.smul_const (f ζ) }
  have H := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
  (F := fun x θ ↦ herglotzRieszKernel 0 x (circleMap 0 R θ) • f (circleMap 0 R θ))
  (F' := fun x θ ↦ (2 * circleMap 0 R θ / (circleMap 0 R θ - x) ^ 2) • f (circleMap 0 R θ))
  (bound := fun θ ↦ (2 * |R| / (r / 2) ^ 2) * ‖f (circleMap 0 R θ)‖)
  (ball_mem_nhds w hhalf)
  (by {
  filter_upwards [ball_mem_nhds w hhalf] with x hx
  exact (h_integrable x hx).aestronglyMeasurable_restrict_uIoc })
  (h_integrable w hwball)
  hdint.aestronglyMeasurable_restrict_uIoc
  (by {
  apply Filter.Eventually.of_forall
  intro θ hθ x hx
  have hz := circleMap_mem_sphere' 0 R θ
  have hl := hlower x hx _ hz
  simp only [norm_smul, norm_div, norm_mul, norm_pow, norm_circleMap_zero, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith [norm_nonneg (circleMap 0 R θ - x)] })
  (hg.norm.const_mul (2 * |R| / (r / 2) ^ 2))
  (by {
  apply Filter.Eventually.of_forall
  intro θ hθ x hx
  exact hder x hx _ (circleMap_mem_sphere' 0 R θ) }))
  simpa only [circleAverage_def, Pi.smul_def] using H.2.const_smul ((2 * π)⁻¹ : ℝ)
