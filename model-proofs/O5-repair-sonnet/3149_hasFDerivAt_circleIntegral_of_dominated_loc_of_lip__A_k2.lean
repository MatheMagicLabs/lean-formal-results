/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     hasFDerivAt_circleIntegral_of_dominated_loc_of_lip
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean, line 64
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
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
  obtain ⟨ε, ε_pos, hε⟩ := Metric.mem_nhds_iff.1 hs
  have hF_meas' : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable
      (fun θ : ℝ ↦ deriv (circleMap c R) θ • F x (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))) :=
    hF_meas.mono fun x hx => aestronglyMeasurable_deriv_circleMap_smul hx
  have hF_int' := (circleIntegrable_iff R).1 hF_int
  have hF'_meas' := aestronglyMeasurable_deriv_circleMap_smul hF'_meas
  have hlip : ∀ t : Set H, t ⊆ s → ∀ θ : ℝ,
      LipschitzOnWith ‖|R| * bound (circleMap c R θ)‖₊
        (fun x => deriv (circleMap c R) θ • F x (circleMap c R θ)) t :=
    fun t ht θ =>
      lipschitzOnWith_deriv_circleMap_smul ((h_lip _ (circleMap_mem_sphere' c R θ)).mono ht)
  have bound_int' : IntervalIntegrable (fun θ => |R| * bound (circleMap c R θ)) volume 0 (2 * π) :=
    (show IntervalIntegrable (fun θ => bound (circleMap c R θ)) volume 0 (2 * π) from
      bound_integrable).const_mul |R|
  have h_diff' : ∀ θ : ℝ, HasFDerivAt
      (fun x => deriv (circleMap c R) θ • F x (circleMap c R θ))
      (deriv (circleMap c R) θ • F' (circleMap c R θ)) x₀ :=
    fun θ => (h_diff _ (circleMap_mem_sphere' c R θ)).const_smul _
  have key : IntervalIntegrable
        (fun θ => deriv (circleMap c R) θ • F' (circleMap c R θ)) volume 0 (2 * π) ∧
      HasFDerivAt
        (fun x => ∫ θ in (0:ℝ)..2 * π, deriv (circleMap c R) θ • F x (circleMap c R θ))
        (∫ θ in (0:ℝ)..2 * π, deriv (circleMap c R) θ • F' (circleMap c R θ)) x₀ := by
    first
    | exact intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip
        (bound := fun θ => |R| * bound (circleMap c R θ)) ε_pos hF_meas' hF_int' hF'_meas'
        (Filter.Eventually.of_forall fun θ _ => hlip _ hε θ) bound_int'
        (Filter.Eventually.of_forall fun θ _ => h_diff' θ)
    | exact intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip
        (bound := fun θ => |R| * bound (circleMap c R θ)) hs hF_meas' hF_int' hF'_meas'
        (Filter.Eventually.of_forall fun θ _ => hlip _ Set.Subset.rfl θ) bound_int'
        (Filter.Eventually.of_forall fun θ _ => h_diff' θ)
  exact ⟨(circleIntegrable_iff R).2 key.1, key.2⟩
