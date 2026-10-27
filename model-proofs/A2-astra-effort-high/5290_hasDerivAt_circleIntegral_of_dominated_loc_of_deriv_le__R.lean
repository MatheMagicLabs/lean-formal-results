/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     hasDerivAt_circleIntegral_of_dominated_loc_of_deriv_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean, line 143
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  let g : ℝ → ℂ := fun θ ↦ circleMap 0 R θ * Complex.I
  have hg_cont : Continuous g := by
    dsimp [g]
    fun_prop
  have hg_norm : ∀ θ, ‖g θ‖ = |R| := by
    intro θ
    simp [g, norm_mul]
  have hcircle (θ : ℝ) : circleMap c R θ ∈ sphere c |R| := by
    have hsub : circleMap c R θ - c = circleMap 0 R θ := by
      simp [circleMap]
    rw [mem_sphere, dist_eq_norm, hsub]
    simpa [g, norm_mul] using hg_norm θ
  have hg_meas : AEStronglyMeasurable g
      (volume.restrict (Ι 0 (2 * π))) :=
    hg_cont.aestronglyMeasurable
  have hFi : IntervalIntegrable
      (fun θ ↦ F x₀ (circleMap c R θ)) volume 0 (2 * π) := hF_int
  have hbi : IntervalIntegrable
      (fun θ ↦ bound (circleMap c R θ)) volume 0 (2 * π) :=
    bound_integrable
  have hsmul {f : ℝ → E}
      (hf : IntervalIntegrable f volume 0 (2 * π)) :
      IntervalIntegrable (fun θ ↦ g θ • f θ) volume 0 (2 * π) := by
    rw [intervalIntegrable_iff] at hf ⊢
    refine (hf.norm.const_mul |R|).mono'
      (hg_meas.smul hf.aestronglyMeasurable) ?_
    filter_upwards [] with θ
    simp only [norm_smul, hg_norm, le_refl]
  have hderiv :
      HasDerivAt
        (fun x ↦ ∫ θ in 0..2 * π, g θ • F x (circleMap c R θ))
        (∫ θ in 0..2 * π, g θ • F' x₀ (circleMap c R θ)) x₀ := by
    refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun x θ ↦ g θ • F x (circleMap c R θ))
      (F' := fun x θ ↦ g θ • F' x (circleMap c R θ))
      (bound := fun θ ↦ |R| * bound (circleMap c R θ))
      hs ?_ (hsmul hFi) (hg_meas.smul hF'_meas) ?_
      (hbi.const_mul |R|) ?_).2
    · filter_upwards [hF_meas] with x hx
      exact hg_meas.smul hx
    · filter_upwards [] with θ
      intros
      rename_i x hx
      rw [norm_smul, hg_norm]
      exact mul_le_mul_of_nonneg_left
        (h_bound _ (hcircle θ) x hx) (abs_nonneg R)
    · filter_upwards [] with θ
      intros
      rename_i x hx
      exact (h_diff _ (hcircle θ) x hx).const_smul (g θ)
  refine ⟨?_, ?_⟩
  · change IntervalIntegrable
      (fun θ ↦ F' x₀ (circleMap c R θ)) volume 0 (2 * π)
    rw [intervalIntegrable_iff]
    refine (intervalIntegrable_iff.mp hbi).mono' hF'_meas ?_
    filter_upwards [] with θ
    exact h_bound _ (hcircle θ) x₀ (mem_of_mem_nhds hs)
  · simpa only [circleIntegral, deriv_circleMap, g, circleMap, zero_add,
      mul_assoc, mul_left_comm, mul_comm] using hderiv
