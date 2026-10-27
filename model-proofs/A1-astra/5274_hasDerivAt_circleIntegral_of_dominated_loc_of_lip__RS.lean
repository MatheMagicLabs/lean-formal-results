/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     hasDerivAt_circleIntegral_of_dominated_loc_of_lip
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean, line 116
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 1 (round 0 = first attempt)
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
  have hcircle (θ : ℝ) : circleMap c R θ ∈ sphere c |R| := by
    simp [Metric.mem_sphere, dist_eq_norm, circleMap, norm_mul,
      Complex.norm_exp, Complex.mul_re]
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
    (bound := fun θ ↦ |R| * bound (circleMap c R θ)) hs
    (hF_meas.mono fun x hx ↦ aestronglyMeasurable_deriv_circleMap_smul hx)
    hF_int.out (aestronglyMeasurable_deriv_circleMap_smul hF'_meas)
    (Filter.Eventually.of_forall fun θ _ ↦
      lipschitzOnWith_deriv_circleMap_smul
        (h_lipsch _ (hcircle θ)))
    ((show IntervalIntegrable (fun θ ↦ bound (circleMap c R θ))
        volume 0 (2 * π) from bound_integrable).const_mul |R|)
    (Filter.Eventually.of_forall fun θ _ ↦
      (h_diff _ (hcircle θ)).const_smul (deriv (circleMap c R) θ))
  exact ⟨(circleIntegrable_iff R).2 h.1, h.2⟩
