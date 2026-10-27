/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     hasFDerivAt_circleIntegral_of_dominated_loc_of_lip
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean, line 64
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm Z, verified in round 2 (round 0 = first attempt)
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
  have hmem (θ : ℝ) : circleMap c R θ ∈ sphere c |R| := by
    simp [mem_sphere, dist_eq_norm, circleMap, norm_mul, Complex.norm_exp]
  have hbase :=
    intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip hs
      hF_meas hF_int hF'_meas
      (Filter.Eventually.of_forall fun θ _ ↦ h_lip _ (hmem θ))
      bound_integrable
      (Filter.Eventually.of_forall fun θ _ ↦ h_diff _ (hmem θ))
  refine ⟨hbase.1, ?_⟩
  let w : ℝ → ℂ := fun θ ↦ circleMap 0 R θ * Complex.I
  have hw : Continuous w := by
    dsimp [w]
    fun_prop
  have hwn (θ : ℝ) : ‖w θ‖ = |R| := by
    simp [w, circleMap, norm_mul, Complex.norm_exp]
  have hweighted_int :
      IntervalIntegrable (fun θ ↦ w θ • F x₀ (circleMap c R θ))
        volume 0 (2 * π) := by
    apply intervalIntegrable_iff.mpr
    have hi := intervalIntegrable_iff.mp hF_int
    refine (hi.norm.const_mul |R|).mono'
      (hw.aestronglyMeasurable.smul hi.aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun θ ↦ by
      simp [norm_smul, hwn]
  have hbound :
      IntervalIntegrable (fun θ ↦ |R| * ‖bound (circleMap c R θ)‖)
        volume 0 (2 * π) := by
    exact bound_integrable.norm.const_mul |R|
  have hweighted :=
    intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip
      (F := fun x θ ↦ w θ • F x (circleMap c R θ))
      (F' := fun θ ↦ w θ • F' (circleMap c R θ))
      (bound := fun θ ↦ |R| * ‖bound (circleMap c R θ)‖)
      hs
      (hF_meas.mono fun x hx ↦ hw.aestronglyMeasurable.smul hx)
      hweighted_int
      (hw.aestronglyMeasurable.smul hF'_meas)
      (Filter.Eventually.of_forall fun θ _ ↦ by
        apply LipschitzOnWith.of_dist_le_mul
        intro x hx y hy
        calc
          dist (w θ • F x (circleMap c R θ))
              (w θ • F y (circleMap c R θ)) =
              |R| * dist (F x (circleMap c R θ))
                (F y (circleMap c R θ)) := by
                  simp only [dist_eq_norm, ← smul_sub, norm_smul, hwn]
          _ ≤ |R| * (‖bound (circleMap c R θ)‖ *
              dist x y) :=
            mul_le_mul_of_nonneg_left
              ((h_lip _ (hmem θ)).dist_le_mul x hx y hy) (abs_nonneg R)
          _ = _ := by
            simp [Real.norm_eq_abs, abs_mul, mul_assoc])
      hbound
      (Filter.Eventually.of_forall fun θ _ ↦
        (h_diff _ (hmem θ)).const_smul (w θ))
  simpa [circleIntegral, w, smul_smul, mul_comm, mul_left_comm, mul_assoc]
    using hweighted.2
