/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     hasFDerivAt_circleIntegral_of_dominated_loc_of_lip
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean, line 64
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
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
  have hmem : ∀ θ : ℝ, circleMap c R θ ∈ sphere c |R| := fun θ => circleMap_mem_sphere' c R θ
  obtain ⟨h1, h2⟩ := intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip
    (μ := volume) (a := 0) (b := 2 * π)
    (F := fun x θ ↦ deriv (circleMap c R) θ • F x (circleMap c R θ))
    (F' := fun θ ↦ deriv (circleMap c R) θ • F' (circleMap c R θ))
    (bound := fun θ ↦ |R| * bound (circleMap c R θ)) hs
    (hF_meas.mono fun x hx ↦ aestronglyMeasurable_deriv_circleMap_smul (f := F x) hx)
    hF_int.out
    (aestronglyMeasurable_deriv_circleMap_smul (f := F') hF'_meas)
    (ae_of_all _ fun θ _ ↦ lipschitzOnWith_deriv_circleMap_smul
      (g := fun x ↦ F x (circleMap c R θ)) (h_lip _ (hmem θ)))
    ((show IntervalIntegrable _ _ _ _ from bound_integrable).const_mul |R|)
    (ae_of_all _ fun θ _ ↦ (h_diff _ (hmem θ)).const_smul (deriv (circleMap c R) θ))
  exact ⟨(circleIntegrable_iff R).2 h1, h2⟩
