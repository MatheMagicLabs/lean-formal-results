/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     hasDerivAt_circleIntegral_of_dominated_loc_of_lip
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean, line 116
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 3 (round 0 = first attempt)
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
  have hmem (θ : ℝ) : circleMap c R θ ∈ sphere c |R| := by
    simp [mem_sphere, dist_eq_norm, circleMap, Complex.norm_exp]
  have hlip :
      ∀ᵐ θ ∂volume, θ ∈ Ι 0 (2 * π) →
        LipschitzOnWith ‖bound (circleMap c R θ)‖₊
          (fun x ↦ F x (circleMap c R θ)) s :=
    Eventually.of_forall fun θ _ ↦ h_lipsch _ (hmem θ)
  have hderiv :
      ∀ᵐ θ ∂volume, θ ∈ Ι 0 (2 * π) →
        HasDerivAt (fun x ↦ F x (circleMap c R θ))
          (F' (circleMap c R θ)) x₀ :=
    Eventually.of_forall fun θ _ ↦ h_diff _ (hmem θ)
  have h :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
      hs hF_meas hF_int hF'_meas hlip bound_integrable hderiv
  refine ⟨h.1, ?_⟩
  have hdcont : Continuous (fun θ : ℝ ↦ deriv (circleMap c R) θ) := by
    simpa only [deriv_circleMap] using
      (continuous_circleMap 0 R).mul_const Complex.I
  have hd_norm (θ : ℝ) : ‖deriv (circleMap c R) θ‖ = |R| := by
    simp [deriv_circleMap, circleMap, norm_mul, Complex.norm_exp]
  have hmeas :
      ∀ᶠ x in 𝓝 x₀,
        AEStronglyMeasurable
          (fun θ : ℝ ↦ deriv (circleMap c R) θ • F x (circleMap c R θ))
          (volume.restrict (Ι 0 (2 * π))) :=
    hF_meas.mono fun x hx ↦ hdcont.aestronglyMeasurable.smul hx
  have hmeas' :
      AEStronglyMeasurable
        (fun θ : ℝ ↦ deriv (circleMap c R) θ • F' (circleMap c R θ))
        (volume.restrict (Ι 0 (2 * π))) :=
    hdcont.aestronglyMeasurable.smul hF'_meas
  have h_integrable :
      IntervalIntegrable
        (fun θ : ℝ ↦ deriv (circleMap c R) θ • F x₀ (circleMap c R θ))
        volume 0 (2 * π) := by
    change IntervalIntegrable (fun θ : ℝ ↦ F x₀ (circleMap c R θ))
      volume 0 (2 * π) at hF_int
    rw [intervalIntegrable_iff]
    apply ((intervalIntegrable_iff.mp hF_int).norm.const_mul |R|).mono'
      hmeas.self_of_nhds
    exact Eventually.of_forall fun θ ↦ by simp [norm_smul, hd_norm]
  have hbound :
      IntervalIntegrable (fun θ : ℝ ↦ |R| * ‖bound (circleMap c R θ)‖)
        volume 0 (2 * π) :=
    bound_integrable.norm.const_mul |R|
  have hlip' :
      ∀ᵐ θ ∂volume, θ ∈ Ι 0 (2 * π) →
        LipschitzOnWith (Real.nnabs (|R| * ‖bound (circleMap c R θ)‖))
          (fun x ↦ deriv (circleMap c R) θ • F x (circleMap c R θ)) s := by
    apply Eventually.of_forall
    intro θ _
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    calc
      dist (deriv (circleMap c R) θ • F x (circleMap c R θ))
          (deriv (circleMap c R) θ • F y (circleMap c R θ)) =
          |R| * dist (F x (circleMap c R θ)) (F y (circleMap c R θ)) := by
            simp [dist_eq_norm, ← smul_sub, norm_smul, hd_norm]
      _ ≤ |R| * (‖bound (circleMap c R θ)‖ * dist x y) :=
        mul_le_mul_of_nonneg_left
          ((h_lipsch _ (hmem θ)).dist_le_mul x hx y hy) (abs_nonneg R)
      _ = ↑(Real.nnabs (|R| * ‖bound (circleMap c R θ)‖)) * dist x y := by
        simp [abs_mul, mul_assoc]
  have hderiv' :
      ∀ᵐ θ ∂volume, θ ∈ Ι 0 (2 * π) →
        HasDerivAt
          (fun x ↦ deriv (circleMap c R) θ • F x (circleMap c R θ))
          (deriv (circleMap c R) θ • F' (circleMap c R θ)) x₀ :=
    Eventually.of_forall fun θ _ ↦ (h_diff _ (hmem θ)).const_smul _
  simpa only [circleIntegral] using
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
      hs hmeas h_integrable hmeas' hlip' hbound hderiv').2
