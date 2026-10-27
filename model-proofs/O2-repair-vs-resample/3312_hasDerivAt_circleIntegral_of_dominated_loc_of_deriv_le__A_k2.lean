/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     hasDerivAt_circleIntegral_of_dominated_loc_of_deriv_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean, line 143
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem hasDerivAt_circleIntegral_of_dominated_loc_of_deriv_le
    {F : 𝕜 → ℂ → E} {F' : 𝕜 → ℂ → E} {x₀ : 𝕜} {s : Set 𝕜} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fun θ : ℝ ↦ F x (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))))
    (hF_int : CircleIntegrable (F x₀) c R)
    (hF'_meas : AEStronglyMeasurable (fun θ : ℝ ↦ F' x₀ (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))))
    (h_bound : ∀ z ∈ sphere c |R|, ∀ x ∈ s, ‖F' x z‖ ≤ bound z)
    (bound_integrable : CircleIntegrable bound c R)
    (h_diff : ∀ z ∈ sphere c |R|, ∀ x ∈ s, HasDerivAt (fun x ↦ F x z) (F' x z) x) :
    CircleIntegrable (F' x₀) c R ∧
      HasDerivAt (fun x ↦ ∮ z in C(c, R), F x z) (∮ z in C(c, R), F' x₀ z) x₀ := by
  rw [circleIntegrable_iff]
  obtain ⟨ε, ε_pos, hε⟩ := Metric.mem_nhds_iff.mp hs
  first
  | exact intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (bound := fun θ ↦ |R| * bound (circleMap c R θ)) hs
      (hF_meas.mono fun _ hx ↦ aestronglyMeasurable_deriv_circleMap_smul hx)
      ((circleIntegrable_iff R).mp hF_int) (aestronglyMeasurable_deriv_circleMap_smul hF'_meas)
      (.of_forall fun θ _ x hx ↦
        norm_deriv_circleMap_smul_le (h_bound _ (circleMap_mem_sphere' c R θ) x hx))
      (bound_integrable.const_mul _)
      (.of_forall fun θ _ x hx ↦ (h_diff _ (circleMap_mem_sphere' c R θ) x hx).const_smul _)
  | exact intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (bound := fun θ ↦ |R| * bound (circleMap c R θ)) ε_pos
      (hF_meas.mono fun _ hx ↦ aestronglyMeasurable_deriv_circleMap_smul hx)
      ((circleIntegrable_iff R).mp hF_int) (aestronglyMeasurable_deriv_circleMap_smul hF'_meas)
      (.of_forall fun θ _ x hx ↦
        norm_deriv_circleMap_smul_le (h_bound _ (circleMap_mem_sphere' c R θ) x (hε hx)))
      (bound_integrable.const_mul _)
      (.of_forall fun θ _ x hx ↦
        (h_diff _ (circleMap_mem_sphere' c R θ) x (hε hx)).const_smul _)
