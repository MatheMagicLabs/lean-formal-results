/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     hasFDerivAt_circleIntegral_of_dominated_loc_of_lip
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean, line 64
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
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
  have hlip1 : ∀ θ : ℝ, LipschitzOnWith ‖bound (circleMap c R θ)‖₊
      (fun x ↦ F x (circleMap c R θ)) s := fun θ => h_lip _ (circleMap_mem_sphere' c R θ)
  have hlip2 : ∀ θ : ℝ, LipschitzOnWith ‖|R| * bound (circleMap c R θ)‖₊
      (fun x ↦ deriv (circleMap c R) θ • F x (circleMap c R θ)) s :=
    fun θ => lipschitzOnWith_deriv_circleMap_smul (hlip1 θ)
  have hdiff1 : ∀ θ : ℝ, HasFDerivAt (fun x ↦ F x (circleMap c R θ))
      (F' (circleMap c R θ)) x₀ :=
    fun θ => h_diff _ (circleMap_mem_sphere' c R θ)
  have hdiff2 : ∀ θ : ℝ, HasFDerivAt (fun x ↦ deriv (circleMap c R) θ • F x (circleMap c R θ))
      (deriv (circleMap c R) θ • F' (circleMap c R θ)) x₀ :=
    fun θ => (hdiff1 θ).const_smul _
  have hm2 : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable
      (fun θ : ℝ ↦ deriv (circleMap c R) θ • F x (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))) :=
    hF_meas.mono fun x hx => aestronglyMeasurable_deriv_circleMap_smul hx
  have hm2' : AEStronglyMeasurable
      (fun θ : ℝ ↦ deriv (circleMap c R) θ • F' (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))) :=
    aestronglyMeasurable_deriv_circleMap_smul hF'_meas
  have hi2 : IntervalIntegrable
      (fun θ : ℝ ↦ deriv (circleMap c R) θ • F x₀ (circleMap c R θ)) volume 0 (2 * π) :=
    hF_int.out
  have hb1 : IntervalIntegrable (fun θ => bound (circleMap c R θ)) volume 0 (2 * π) :=
    bound_integrable
  have hb2 : IntervalIntegrable (fun θ => |R| * bound (circleMap c R θ)) volume 0 (2 * π) :=
    hb1.const_mul _
  have hi1 : IntervalIntegrable (fun θ => F x₀ (circleMap c R θ)) volume 0 (2 * π) := hF_int
  obtain ⟨ε, ε_pos, hε⟩ := Metric.mem_nhds_iff.mp hs
  have h1 : CircleIntegrable F' c R := by
    first
    | exact (intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip hs hF_meas hi1
        hF'_meas (Eventually.of_forall fun θ _ => hlip1 θ) hb1
        (Eventually.of_forall fun θ _ => hdiff1 θ)).1
    | exact (intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip ε_pos hF_meas hi1
        hF'_meas (Eventually.of_forall fun θ _ => (hlip1 θ).mono hε) hb1
        (Eventually.of_forall fun θ _ => hdiff1 θ)).1
  refine ⟨h1, ?_⟩
  unfold circleIntegral
  first
  | exact (intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip hs hm2 hi2
      hm2' (Eventually.of_forall fun θ _ => hlip2 θ) hb2
      (Eventually.of_forall fun θ _ => hdiff2 θ)).2
  | exact (intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip ε_pos hm2 hi2
      hm2' (Eventually.of_forall fun θ _ => (hlip2 θ).mono hε) hb2
      (Eventually.of_forall fun θ _ => hdiff2 θ)).2
