/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     hasFDerivAt_circleIntegral_of_dominated_loc_of_lip
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean, line 64
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  let μ := volume.restrict (Ι 0 (2 * π))
  let w : ℝ → ℂ := fun θ ↦ circleMap 0 R θ * Complex.I
  have hmem (θ : ℝ) : circleMap c R θ ∈ sphere c |R| := by
    simp [mem_sphere, dist_eq_norm, circleMap, norm_mul, Complex.norm_exp]
  have hw_norm (θ : ℝ) : ‖w θ‖ = |R| := by
    simp [w, circleMap, norm_mul, Complex.norm_exp]
  have hw_meas : AEStronglyMeasurable w μ := by
    have hw_cont : Continuous w := by
      dsimp [w]
      fun_prop
    exact hw_cont.aestronglyMeasurable
  have hi : Integrable (fun θ : ℝ ↦ F x₀ (circleMap c R θ)) μ := by
    simpa only [CircleIntegrable, intervalIntegrable_iff, IntegrableOn, μ]
      using hF_int
  have hb : Integrable (fun θ : ℝ ↦ bound (circleMap c R θ)) μ := by
    simpa only [CircleIntegrable, intervalIntegrable_iff, IntegrableOn, μ]
      using bound_integrable
  have hl :
      ∀ᵐ θ : ℝ ∂μ,
        LipschitzOnWith ‖bound (circleMap c R θ)‖₊
          (fun x ↦ F x (circleMap c R θ)) s :=
    Filter.Eventually.of_forall fun θ ↦ h_lip _ (hmem θ)
  have hd :
      ∀ᵐ θ : ℝ ∂μ,
        HasFDerivAt (fun x ↦ F x (circleMap c R θ))
          (F' (circleMap c R θ)) x₀ :=
    Filter.Eventually.of_forall fun θ ↦ h_diff _ (hmem θ)
  have hu := hasFDerivAt_integral_of_dominated_loc_of_lip
    hs hF_meas hi hF'_meas hl hb hd
  refine ⟨?_, ?_⟩
  · simpa only [CircleIntegrable, intervalIntegrable_iff, IntegrableOn, μ]
      using hu.1
  · have hwm :
        ∀ᶠ x in 𝓝 x₀,
          AEStronglyMeasurable (fun θ : ℝ ↦ w θ • F x (circleMap c R θ)) μ := by
      filter_upwards [hF_meas] with x hx
      exact hw_meas.smul hx
    have hwi :
        Integrable (fun θ : ℝ ↦ w θ • F x₀ (circleMap c R θ)) μ := by
      refine (hi.norm.const_mul |R|).mono'
        (hw_meas.smul hi.aestronglyMeasurable) ?_
      filter_upwards [] with θ
      simp only [norm_smul, hw_norm, le_refl]
    have hwb :
        Integrable (fun θ : ℝ ↦ ‖w θ‖ * bound (circleMap c R θ)) μ := by
      simpa only [hw_norm] using hb.const_mul |R|
    have hwl :
        ∀ᵐ θ : ℝ ∂μ,
          LipschitzOnWith ‖‖w θ‖ * bound (circleMap c R θ)‖₊
            (fun x ↦ w θ • F x (circleMap c R θ)) s := by
      filter_upwards [hl] with θ hθ
      rw [lipschitzOnWith_iff_dist_le_mul] at hθ ⊢
      intro x hx y hy
      simpa [dist_eq_norm, ← smul_sub, norm_smul, norm_mul, mul_assoc] using
        mul_le_mul_of_nonneg_left (hθ x hx y hy) (norm_nonneg (w θ))
    have hwd :
        ∀ᵐ θ : ℝ ∂μ,
          HasFDerivAt (fun x ↦ w θ • F x (circleMap c R θ))
            (w θ • F' (circleMap c R θ)) x₀ := by
      filter_upwards [hd] with θ hθ
      exact hθ.const_smul (w θ)
    have hw := hasFDerivAt_integral_of_dominated_loc_of_lip
      hs hwm hwi (hw_meas.smul hF'_meas) hwl hwb hwd
    have hle : (0 : ℝ) ≤ 2 * π := by positivity
    simpa [circleIntegral, w, circleMap, μ,
      intervalIntegral.integral_of_le hle, uIoc_of_le hle] using hw.2
