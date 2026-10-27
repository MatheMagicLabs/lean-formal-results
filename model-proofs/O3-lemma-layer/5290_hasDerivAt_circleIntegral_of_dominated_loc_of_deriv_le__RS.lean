/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     hasDerivAt_circleIntegral_of_dominated_loc_of_deriv_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean, line 143
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
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
  obtain ⟨h1, h2⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x θ ↦ deriv (circleMap c R) θ • F x (circleMap c R θ))
    (F' := fun x θ ↦ deriv (circleMap c R) θ • F' x (circleMap c R θ))
    (bound := fun θ ↦ |R| * bound (circleMap c R θ)) (μ := volume) (a := 0) (b := 2 * π) hs
    (hF_meas.mono fun x hx ↦ aestronglyMeasurable_deriv_circleMap_smul hx)
    hF_int.out
    (aestronglyMeasurable_deriv_circleMap_smul hF'_meas)
    (ae_of_all _ fun θ _ x hx ↦ by
      rw [norm_smul, deriv_circleMap, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one]
      exact mul_le_mul_of_nonneg_left (h_bound _ (circleMap_mem_sphere' _ _ _) x hx)
        (abs_nonneg R))
    (((circleIntegrable_def _ _ _).1 bound_integrable).const_mul |R|)
    (ae_of_all _ fun θ _ x hx ↦
      (h_diff _ (circleMap_mem_sphere' _ _ _) x hx).const_smul _)
  refine ⟨(circleIntegrable_iff R).2 h1, ?_⟩
  simpa only [circleIntegral] using h2
