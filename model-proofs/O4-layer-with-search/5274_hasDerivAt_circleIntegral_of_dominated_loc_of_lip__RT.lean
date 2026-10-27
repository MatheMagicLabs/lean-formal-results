/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     hasDerivAt_circleIntegral_of_dominated_loc_of_lip
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean, line 116
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open MeasureTheory Metric Set Filter
open scoped Real Topology Interval NNReal
variable {𝕜 E H : Type*} [RCLike 𝕜]
section Aux
end Aux

theorem hasDerivAt_circleIntegral_of_dominated_loc_of_lip
    {F : 𝕜 → ℂ → E} {F' : ℂ → E} {x₀ : 𝕜} {s : Set 𝕜} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fun θ : ℝ ↦ F x (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))))
    (hF_int : CircleIntegrable (F x₀) c R)
    (hF'_meas : AEStronglyMeasurable (fun θ : ℝ ↦ F' (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))))
    (h_lipsch : ∀ z ∈ sphere c |R|, LipschitzOnWith ‖bound z‖₊ (fun x ↦ F x z) s)
    (bound_integrable : CircleIntegrable bound c R)
    (h_diff : ∀ z ∈ sphere c |R|, HasDerivAt (fun x ↦ F x z) (F' z) x₀) :
    CircleIntegrable F' c R ∧
      HasDerivAt (fun x ↦ ∮ z in C(c, R), F x z) (∮ z in C(c, R), F' z) x₀ := by
  have hR : ∀ θ : ℝ, ‖deriv (circleMap c R) θ‖ = |R| := by
    intro θ
    simp [deriv_circleMap]
  have hcont : Continuous fun θ : ℝ ↦ deriv (circleMap c R) θ := by
    simp only [deriv_circleMap]
    exact (continuous_circleMap 0 R).mul continuous_const
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip (μ := volume)
    (a := 0) (b := 2 * π)
    (F := fun x θ ↦ deriv (circleMap c R) θ • F x (circleMap c R θ))
    (F' := fun θ ↦ deriv (circleMap c R) θ • F' (circleMap c R θ))
    (bound := fun θ ↦ |R| * ‖bound (circleMap c R θ)‖) hs ?_ ?_ ?_ ?_ ?_ ?_
  · exact ⟨(circleIntegrable_iff R).2 h.1, h.2⟩
  · exact hF_meas.mono fun x hx ↦ hcont.aestronglyMeasurable.smul hx
  · exact (circleIntegrable_iff R).1 hF_int
  · exact hcont.aestronglyMeasurable.smul hF'_meas
  · refine ae_of_all _ fun θ _ ↦ ?_
    have hz := h_lipsch _ (circleMap_mem_sphere' c R θ)
    rw [lipschitzOnWith_iff_norm_sub_le] at hz ⊢
    intro x hx y hy
    simp only [← smul_sub, norm_smul, hR, Real.coe_nnabs]
    rw [abs_of_nonneg (show (0:ℝ) ≤ |R| * ‖bound (circleMap c R θ)‖ by positivity),
      mul_assoc]
    have := hz hx hy
    rw [coe_nnnorm] at this
    exact mul_le_mul_of_nonneg_left this (abs_nonneg R)
  · exact (IntervalIntegrable.norm bound_integrable).const_mul |R|
  · exact ae_of_all _ fun θ _ ↦
      (h_diff _ (circleMap_mem_sphere' c R θ)).const_smul (deriv (circleMap c R) θ)
