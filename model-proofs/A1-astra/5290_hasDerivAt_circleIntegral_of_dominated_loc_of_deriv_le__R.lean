/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     hasDerivAt_circleIntegral_of_dominated_loc_of_deriv_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean, line 143
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 1 (round 0 = first attempt)
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
  have hle : (0 : ℝ) ≤ 2 * π := by positivity
  have hx₀ : x₀ ∈ s := mem_of_mem_nhds hs
  have hcircle (θ : ℝ) : circleMap c R θ ∈ sphere c |R| := by
    simp [mem_sphere, dist_eq_norm, circleMap, norm_mul, Complex.norm_exp]
  have hw_cont : Continuous (fun θ : ℝ ↦ deriv (circleMap c R) θ) := by
    simp only [deriv_circleMap]
    fun_prop
  have hw_meas :
      AEStronglyMeasurable (fun θ : ℝ ↦ deriv (circleMap c R) θ)
        (volume.restrict (Ι 0 (2 * π))) :=
    hw_cont.aestronglyMeasurable
  have hw_norm (θ : ℝ) : ‖deriv (circleMap c R) θ‖ = |R| := by
    simp [deriv_circleMap, circleMap, norm_mul, Complex.norm_exp]
  have hFi :
      Integrable (fun θ : ℝ ↦ F x₀ (circleMap c R θ))
        (volume.restrict (Ι 0 (2 * π))) := by
    simpa only [CircleIntegrable, intervalIntegrable_iff, IntegrableOn] using hF_int
  have hbi :
      Integrable (fun θ : ℝ ↦ bound (circleMap c R θ))
        (volume.restrict (Ι 0 (2 * π))) := by
    simpa only [CircleIntegrable, intervalIntegrable_iff, IntegrableOn]
      using bound_integrable
  have hF'i :
      Integrable (fun θ : ℝ ↦ F' x₀ (circleMap c R θ))
        (volume.restrict (Ι 0 (2 * π))) := by
    apply hbi.mono' hF'_meas
    exact Filter.Eventually.of_forall fun θ ↦
      h_bound _ (hcircle θ) x₀ hx₀
  have hwFi :
      Integrable
        (fun θ : ℝ ↦ deriv (circleMap c R) θ • F x₀ (circleMap c R θ))
        (volume.restrict (Ι 0 (2 * π))) := by
    apply (hFi.norm.const_mul |R|).mono'
      (hw_meas.smul hFi.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun θ ↦
      (calc
        ‖deriv (circleMap c R) θ • F x₀ (circleMap c R θ)‖ =
            ‖deriv (circleMap c R) θ‖ * ‖F x₀ (circleMap c R θ)‖ :=
          norm_smul _ _
        _ = |R| * ‖F x₀ (circleMap c R θ)‖ := by rw [hw_norm]).le
  have hmain :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun x θ ↦ deriv (circleMap c R) θ • F x (circleMap c R θ))
      (F' := fun x θ ↦ deriv (circleMap c R) θ • F' x (circleMap c R θ))
      (bound := fun θ ↦ |R| * bound (circleMap c R θ))
      hs
      (hF_meas.mono fun x hx ↦ hw_meas.smul hx)
      hwFi
      (hw_meas.smul hF'_meas)
      (Filter.Eventually.of_forall fun θ x hx ↦ show
        ‖deriv (circleMap c R) θ • F' x (circleMap c R θ)‖ ≤
          |R| * bound (circleMap c R θ) from by
        rw [norm_smul, hw_norm]
        exact mul_le_mul_of_nonneg_left
          (h_bound _ (hcircle θ) x hx) (abs_nonneg R))
      (hbi.const_mul |R|)
      (Filter.Eventually.of_forall fun θ x hx ↦
        (h_diff _ (hcircle θ) x hx).const_smul (deriv (circleMap c R) θ))
  refine ⟨?_, ?_⟩
  · simpa only [CircleIntegrable, intervalIntegrable_iff, IntegrableOn] using hF'i
  · simpa only [circleIntegral, deriv_circleMap,
      intervalIntegral.integral_of_le hle, uIoc_of_le hle] using hmain.2
