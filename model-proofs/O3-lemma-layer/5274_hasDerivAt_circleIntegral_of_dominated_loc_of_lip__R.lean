/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     hasDerivAt_circleIntegral_of_dominated_loc_of_lip
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean, line 116
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
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
  obtain ⟨ε, ε_pos, hε⟩ := Metric.mem_nhds_iff.1 hs
  have hd : deriv (circleMap c R) = fun θ => circleMap 0 R θ * Complex.I :=
    funext (deriv_circleMap c R)
  have hdc : Continuous (deriv (circleMap c R)) := by
    rw [hd]; exact (continuous_circleMap 0 R).mul continuous_const
  have h1 : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable
      (fun θ : ℝ => deriv (circleMap c R) θ • F x (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))) :=
    hF_meas.mono fun x hx => hdc.aestronglyMeasurable.smul hx
  have h2 : IntervalIntegrable
      (fun θ : ℝ => deriv (circleMap c R) θ • F x₀ (circleMap c R θ)) volume 0 (2 * π) :=
    (circleIntegrable_iff R).1 hF_int
  have h3 : AEStronglyMeasurable
      (fun θ : ℝ => deriv (circleMap c R) θ • F' (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))) :=
    hdc.aestronglyMeasurable.smul hF'_meas
  have h4 : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι 0 (2 * π) →
      LipschitzOnWith (Real.nnabs (|R| * ‖bound (circleMap c R t)‖))
        (fun x => deriv (circleMap c R) t • F x (circleMap c R t)) (ball x₀ ε) := by
    refine ae_of_all _ fun t _ => ?_
    have hz : circleMap c R t ∈ sphere c |R| := circleMap_mem_sphere' c R t
    have hL := (h_lipsch _ hz).mono hε
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have h1 := hL.dist_le_mul x hx y hy
    rw [coe_nnnorm] at h1
    beta_reduce
    rw [dist_smul₀, Real.coe_nnabs, deriv_circleMap, norm_mul, Complex.norm_I, mul_one,
      norm_circleMap_zero, abs_mul, abs_abs, abs_norm, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg R)
  have hb : IntervalIntegrable (fun θ => bound (circleMap c R θ)) volume 0 (2 * π) :=
    bound_integrable
  have h5 : IntervalIntegrable (fun t => |R| * ‖bound (circleMap c R t)‖) volume 0 (2 * π) :=
    (IntervalIntegrable.norm hb).const_mul _
  have h6 : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι 0 (2 * π) →
      HasDerivAt (fun x => deriv (circleMap c R) t • F x (circleMap c R t))
        (deriv (circleMap c R) t • F' (circleMap c R t)) x₀ :=
    ae_of_all _ fun t _ => (h_diff _ (circleMap_mem_sphere' c R t)).const_smul _
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
    (ball_mem_nhds x₀ ε_pos) h1 h2 h3 h4 h5 h6
  exact ⟨(circleIntegrable_iff R).2 h.1, h.2⟩
