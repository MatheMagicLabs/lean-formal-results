/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     hasDerivAt_circleIntegral_of_dominated_loc_of_lip
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean, line 116
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
  have h_diff' : ∀ z ∈ sphere c |R|,
      HasFDerivAt (fun x ↦ F x z) ((1 : 𝕜 →L[𝕜] 𝕜).smulRight (F' z)) x₀ :=
    fun z hz ↦ (h_diff z hz).hasFDerivAt
  have hm : AEStronglyMeasurable
      (fun θ : ℝ ↦ (1 : 𝕜 →L[𝕜] 𝕜).smulRight (F' (circleMap c R θ)))
      (volume.restrict (Ι 0 (2 * π))) := by
    exact (ContinuousLinearMap.smulRightL 𝕜 𝕜 E 1).continuous.comp_aestronglyMeasurable
      hF'_meas
  obtain ⟨hF'_int, key⟩ :=
    hasFDerivAt_circleIntegral_of_dominated_loc_of_lip
      (F' := fun z ↦ (1 : 𝕜 →L[𝕜] 𝕜).smulRight (F' z))
      hs hF_meas hF_int hm h_lipsch bound_integrable h_diff'
  have hF'_int' : CircleIntegrable F' c R := by
    rw [circleIntegrable_def] at hF'_int ⊢
    refine hF'_int.mono_fun hF'_meas (Eventually.of_forall fun θ ↦ ?_)
    simp [ContinuousLinearMap.norm_smulRight_apply]
  refine ⟨hF'_int', ?_⟩
  have := key.hasDerivAt
  convert this using 1
  simp only [circleIntegral]
  rw [ContinuousLinearMap.intervalIntegral_apply hF'_int.out]
  simp
