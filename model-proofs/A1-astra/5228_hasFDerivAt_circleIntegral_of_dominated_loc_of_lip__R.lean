/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     hasFDerivAt_circleIntegral_of_dominated_loc_of_lip
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean, line 64
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  have hmem (θ : ℝ) : circleMap c R θ ∈ sphere c |R| := by
    simp [mem_sphere, dist_eq_norm, circleMap, Complex.norm_exp]
  have hfi :
      IntervalIntegrable (fun θ : ℝ ↦ F x₀ (circleMap c R θ))
        volume 0 (2 * π) := hF_int
  have hbi :
      IntervalIntegrable (fun θ : ℝ ↦ ‖bound (circleMap c R θ)‖)
        volume 0 (2 * π) :=
    bound_integrable.norm
  have hu := intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip
    hs hF_meas hfi hF'_meas
    (Filter.Eventually.of_forall fun θ _ ↦ h_lip _ (hmem θ))
    bound_integrable
    (Filter.Eventually.of_forall fun θ _ ↦ h_diff _ (hmem θ))
  refine ⟨hu.1, ?_⟩
  have hw (g : ℝ → ℂ) (hg : Continuous g) :
      HasFDerivAt
        (fun x ↦ ∫ θ in 0..2 * π, g θ • F x (circleMap c R θ))
        (∫ θ in 0..2 * π, g θ • F' (circleMap c R θ)) x₀ := by
    have hm :
        ∀ᶠ x in 𝓝 x₀,
          AEStronglyMeasurable
            (fun θ : ℝ ↦ g θ • F x (circleMap c R θ))
            (volume.restrict (Ι 0 (2 * π))) :=
      hF_meas.mono fun x hx ↦ hg.aestronglyMeasurable.smul hx
    have hi :
        IntervalIntegrable
          (fun θ : ℝ ↦ g θ • F x₀ (circleMap c R θ))
          volume 0 (2 * π) :=
      hfi.continuousOn_smul hg.continuousOn
    have hmi :
        AEStronglyMeasurable
          (fun θ : ℝ ↦ g θ • F' (circleMap c R θ))
          (volume.restrict (Ι 0 (2 * π))) :=
      hg.aestronglyMeasurable.smul hF'_meas
    have hb :
        IntervalIntegrable
          (fun θ : ℝ ↦ ‖g θ‖ * ‖bound (circleMap c R θ)‖)
          volume 0 (2 * π) :=
      hbi.continuousOn_mul hg.norm.continuousOn
    have hl :
        ∀ᵐ θ ∂volume, θ ∈ Ι 0 (2 * π) →
          LipschitzOnWith
            ‖‖g θ‖ * ‖bound (circleMap c R θ)‖‖₊
            (fun x ↦ g θ • F x (circleMap c R θ)) s := by
      filter_upwards [] with θ
      intro _
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro x hx y hy
      have hh :=
        (lipschitzOnWith_iff_dist_le_mul.mp (h_lip _ (hmem θ))) x hx y hy
      calc
        dist (g θ • F x (circleMap c R θ))
            (g θ • F y (circleMap c R θ)) =
            ‖g θ‖ * dist (F x (circleMap c R θ)) (F y (circleMap c R θ)) := by
              simp [dist_eq_norm, ← smul_sub, norm_smul]
        _ ≤ ‖g θ‖ * (‖bound (circleMap c R θ)‖ * dist x y) := by
              exact mul_le_mul_of_nonneg_left hh (norm_nonneg _)
        _ = _ := by simp [mul_assoc]
    exact
      (intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip
        hs hm hi hmi hl hb
        (Filter.Eventually.of_forall fun θ _ ↦
          (h_diff _ (hmem θ)).const_smul (g θ))).2
  unfold circleIntegral
  apply hw
  change Continuous (fun θ : ℝ ↦ deriv (circleMap c R) θ)
  simp only [deriv_circleMap]
  unfold circleMap
  fun_prop
