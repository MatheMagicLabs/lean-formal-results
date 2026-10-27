/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     hasFDerivAt_circleIntegral_of_dominated_loc_of_lip
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean, line 64
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
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
  have hF_int' : IntervalIntegrable (fun θ : ℝ ↦ F x₀ (circleMap c R θ)) volume 0 (2 * π) :=
    hF_int
  have hbound' : IntervalIntegrable (fun θ : ℝ ↦ bound (circleMap c R θ)) volume 0 (2 * π) :=
    bound_integrable
  have hbound_norm : ∀ z ∈ sphere c |R|, ‖F' z‖ ≤ ‖bound z‖ := fun z hz =>
    (h_diff z hz).le_of_lipschitzOn hs (h_lip z hz)
  have hF'int : CircleIntegrable F' c R := by
    refine IntervalIntegrable.mono_fun' hbound'.norm hF'_meas ?_
    refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun θ _ => ?_)
    exact hbound_norm _ (circleMap_mem_sphere' c R θ)
  refine ⟨hF'int, ?_⟩
  have h1 : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable
      (fun θ : ℝ ↦ deriv (circleMap c R) θ • F x (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))) :=
    hF_meas.mono fun x hx => aestronglyMeasurable_deriv_circleMap_smul hx
  have h2 : IntervalIntegrable
      (fun θ : ℝ ↦ deriv (circleMap c R) θ • F x₀ (circleMap c R θ)) volume 0 (2 * π) := by
    refine IntervalIntegrable.mono_fun' (hF_int'.norm.const_mul |R|)
      (aestronglyMeasurable_deriv_circleMap_smul
        (intervalIntegrable_iff.1 hF_int').aestronglyMeasurable)
      (Eventually.of_forall fun θ => norm_deriv_circleMap_smul_le le_rfl)
  have h3 := aestronglyMeasurable_deriv_circleMap_smul hF'_meas
  have h4 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Ι 0 (2 * π) →
      LipschitzOnWith (Real.nnabs (|R| * bound (circleMap c R θ)))
        (fun x => deriv (circleMap c R) θ • F x (circleMap c R θ)) s := by
    refine Eventually.of_forall fun θ _ => ?_
    have := lipschitzOnWith_deriv_circleMap_smul (c := c) (R := R) (θ := θ)
      (h_lip _ (circleMap_mem_sphere' c R θ))
    exact this
  have h5 : IntervalIntegrable (fun θ : ℝ ↦ |R| * bound (circleMap c R θ)) volume 0 (2 * π) :=
    hbound'.const_mul |R|
  have h6 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Ι 0 (2 * π) →
      HasFDerivAt (fun x => deriv (circleMap c R) θ • F x (circleMap c R θ))
        (deriv (circleMap c R) θ • F' (circleMap c R θ)) x₀ := by
    refine Eventually.of_forall fun θ _ => ?_
    exact (h_diff _ (circleMap_mem_sphere' c R θ)).const_smul (deriv (circleMap c R) θ)
  have := intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip
    (μ := volume) (a := 0) (b := 2 * π)
    (F := fun x θ => deriv (circleMap c R) θ • F x (circleMap c R θ))
    (F' := fun θ => deriv (circleMap c R) θ • F' (circleMap c R θ))
    (bound := fun θ => |R| * bound (circleMap c R θ)) (x₀ := x₀)
    hs h1 h2 h3 h4 h5 h6
  exact this.2
