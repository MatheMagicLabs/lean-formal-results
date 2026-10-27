/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     hasFDerivAt_circleIntegral_of_dominated_loc_of_lip
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean, line 64
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
  have h := intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip (μ := volume)
    (a := 0) (b := 2 * π)
    (F := fun x θ => deriv (circleMap c R) θ • F x (circleMap c R θ))
    (F' := fun θ => deriv (circleMap c R) θ • F' (circleMap c R θ))
    (bound := fun θ => |R| * bound (circleMap c R θ)) hs
    (hF_meas.mono fun x hx => aestronglyMeasurable_deriv_circleMap_smul hx)
    hF_int.out
    (aestronglyMeasurable_deriv_circleMap_smul hF'_meas)
    (Filter.Eventually.of_forall fun θ _ => by
      convert lipschitzOnWith_deriv_circleMap_smul (h_lip _ (circleMap_mem_sphere' c R θ)) using 1
      ext
      simp)
    (((circleIntegrable_def _ _ _).1 bound_integrable).const_mul |R|)
    (Filter.Eventually.of_forall fun θ _ =>
      (h_diff _ (circleMap_mem_sphere' c R θ)).const_smul (deriv (circleMap c R) θ))
  exact ⟨(circleIntegrable_iff R).2 h.1, h.2⟩
