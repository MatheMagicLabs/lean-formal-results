/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     hasDerivAt_circleIntegral_of_dominated_loc_of_deriv_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean, line 143
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
  have hcircle (θ : ℝ) : circleMap c R θ ∈ sphere c |R| := by
    simp [mem_sphere, dist_eq_norm, circleMap, Complex.norm_exp]
  have hc : Continuous (fun θ : ℝ ↦ deriv (circleMap c R) θ) := by
    simp only [deriv_circleMap]
    fun_prop
  have hn (θ : ℝ) : ‖deriv (circleMap c R) θ‖ = |R| := by
    simp [deriv_circleMap, circleMap, norm_mul, Complex.norm_exp]
  have hi : IntervalIntegrable (fun θ : ℝ ↦ F x₀ (circleMap c R θ))
      volume 0 (2 * π) := hF_int
  have hb : IntervalIntegrable (fun θ : ℝ ↦ bound (circleMap c R θ))
      volume 0 (2 * π) := bound_integrable
  have h₁ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun x θ ↦ F' x (circleMap c R θ))
    hs hF_meas hi hF'_meas
    (Filter.Eventually.of_forall fun θ _ x hx ↦ h_bound _ (hcircle θ) x hx)
    hb
    (Filter.Eventually.of_forall fun θ _ x hx ↦ h_diff _ (hcircle θ) x hx)
  refine ⟨h₁.1, ?_⟩
  have hm :
      ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable
        (fun θ : ℝ ↦ deriv (circleMap c R) θ • F x (circleMap c R θ))
        (volume.restrict (Ι 0 (2 * π))) := by
    filter_upwards [hF_meas] with x hx
    exact hc.aestronglyMeasurable.smul hx
  have hiw : IntervalIntegrable
      (fun θ : ℝ ↦ deriv (circleMap c R) θ • F x₀ (circleMap c R θ))
      volume 0 (2 * π) := by
    first
    | exact hi.continuousOn_smul hc.continuousOn
    | exact hc.continuousOn.smul_intervalIntegrable hi
    | exact hc.smul_intervalIntegrable hi
  have hmw : AEStronglyMeasurable
      (fun θ : ℝ ↦ deriv (circleMap c R) θ • F' x₀ (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))) :=
    hc.aestronglyMeasurable.smul hF'_meas
  have h₂ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun x θ ↦ deriv (circleMap c R) θ • F' x (circleMap c R θ))
    hs hm hiw hmw
    (Filter.Eventually.of_forall fun θ _ x hx ↦
      show ‖deriv (circleMap c R) θ • F' x (circleMap c R θ)‖ ≤
          |R| * bound (circleMap c R θ) from by
        rw [norm_smul, hn]
        exact mul_le_mul_of_nonneg_left
          (h_bound _ (hcircle θ) x hx) (abs_nonneg R))
    (hb.const_mul |R|)
    (Filter.Eventually.of_forall fun θ _ x hx ↦
      (h_diff _ (hcircle θ) x hx).const_smul (deriv (circleMap c R) θ))
  simpa only [circleIntegral] using h₂.2
