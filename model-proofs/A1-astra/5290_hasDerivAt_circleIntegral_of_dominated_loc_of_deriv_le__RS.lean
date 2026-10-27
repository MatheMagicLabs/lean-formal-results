/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     hasDerivAt_circleIntegral_of_dominated_loc_of_deriv_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean, line 143
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
  have hmem (θ : ℝ) : circleMap c R θ ∈ sphere c |R| := by
    rw [mem_sphere, dist_eq_norm]
    simpa [circleMap] using norm_circleMap_zero R θ
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x θ ↦ deriv (circleMap c R) θ • F x (circleMap c R θ))
    (F' := fun x θ ↦ deriv (circleMap c R) θ • F' x (circleMap c R θ))
    (bound := fun θ ↦ |R| * bound (circleMap c R θ))
    hs
    (hF_meas.mono fun x hx ↦ aestronglyMeasurable_deriv_circleMap_smul hx)
    hF_int.out
    (aestronglyMeasurable_deriv_circleMap_smul hF'_meas)
    (by
      filter_upwards [] with θ
      intro hθ x hx
      exact norm_deriv_circleMap_smul_le (h_bound _ (hmem θ) x hx))
    (((circleIntegrable_def bound c R).mp bound_integrable).const_mul |R|)
    (by
      filter_upwards [] with θ
      intro hθ x hx
      exact (h_diff _ (hmem θ) x hx).const_smul _)
  exact ⟨(circleIntegrable_iff R).mpr h.1, h.2⟩
