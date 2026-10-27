/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     hasFDerivAt_circleIntegral_of_dominated_loc_of_lip
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean, line 64
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open MeasureTheory Metric Set Filter
open scoped Real Topology Interval NNReal
variable {𝕜 E H : Type*} [RCLike 𝕜]
section Aux
end Aux

theorem hasFDerivAt_circleIntegral_of_dominated_loc_of_lip
    {F : H → ℂ → E} {F' : ℂ → H →L[𝕜] E} {x₀ : H} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fun θ : ℝ ↦ F x (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))))
    (hF_int : CircleIntegrable (F x₀) c R)
    (hF'_meas : AEStronglyMeasurable (fun θ : ℝ ↦ F' (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))))
    (h_lip : ∀ z ∈ sphere c |R|, LipschitzOnWith ‖bound z‖₊ (fun x ↦ F x z) s)
    (bound_integrable : CircleIntegrable bound c R)
    (h_diff : ∀ z ∈ sphere c |R|, HasFDerivAt (fun x ↦ F x z) (F' z) x₀) :
    CircleIntegrable F' c R ∧
      HasFDerivAt (fun x ↦ ∮ z in C(c, R), F x z) (∮ z in C(c, R), F' z) x₀ := by
  obtain ⟨ε, ε_pos, hε⟩ := Metric.mem_nhds_iff.1 hs
  have hcont : Continuous fun θ : ℝ => circleMap 0 R θ * Complex.I :=
    (continuous_circleMap 0 R).mul continuous_const
  have h1 : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable
      (fun θ : ℝ => (circleMap 0 R θ * Complex.I) • F x (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))) := by
    filter_upwards [hF_meas] with x hx
    exact hcont.aestronglyMeasurable.smul hx
  have h2 : IntervalIntegrable
      (fun θ : ℝ => (circleMap 0 R θ * Complex.I) • F x₀ (circleMap c R θ)) volume 0 (2 * π) := by
    simpa only [deriv_circleMap] using (circleIntegrable_iff R).1 hF_int
  have h3 : AEStronglyMeasurable
      (fun θ : ℝ => (circleMap 0 R θ * Complex.I) • F' (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))) :=
    hcont.aestronglyMeasurable.smul hF'_meas
  have h4 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Ι 0 (2 * π) →
      LipschitzOnWith (Real.nnabs (|R| * ‖bound (circleMap c R θ)‖))
        (fun x => (circleMap 0 R θ * Complex.I) • F x (circleMap c R θ)) (ball x₀ ε) := by
    refine Filter.Eventually.of_forall fun θ _ => ?_
    have hz := circleMap_mem_sphere' c R θ
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have h1 := (h_lip _ hz).dist_le_mul x (hε hx) y (hε hy)
    rw [coe_nnnorm] at h1
    rw [dist_smul₀, Real.coe_nnabs, abs_of_nonneg (by positivity), norm_mul,
      norm_circleMap_zero, Complex.norm_I, mul_one, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg R)
  have hb : IntervalIntegrable (fun θ => bound (circleMap c R θ)) volume 0 (2 * π) :=
    bound_integrable
  have h5 : IntervalIntegrable (fun θ : ℝ => |R| * ‖bound (circleMap c R θ)‖) volume 0 (2 * π) :=
    hb.norm.const_mul |R|
  have h6 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Ι 0 (2 * π) →
      HasFDerivAt (fun x => (circleMap 0 R θ * Complex.I) • F x (circleMap c R θ))
        ((circleMap 0 R θ * Complex.I) • F' (circleMap c R θ)) x₀ := by
    refine Filter.Eventually.of_forall fun θ _ => ?_
    exact (h_diff _ (circleMap_mem_sphere' c R θ)).const_smul _
  have key := intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip
    (Metric.ball_mem_nhds x₀ ε_pos) h1 h2 h3 h4 h5 h6
  refine ⟨(circleIntegrable_iff R).2 ?_, ?_⟩
  · simpa only [deriv_circleMap] using key.1
  · simpa only [circleIntegral, deriv_circleMap] using key.2
