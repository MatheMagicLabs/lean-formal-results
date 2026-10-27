/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     hasDerivAt_circleIntegral_of_dominated_loc_of_lip
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean, line 116
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 1 (round 0 = first attempt)
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
  have hcont : Continuous (fun θ : ℝ ↦ deriv (circleMap c R) θ) := by
    simp only [deriv_circleMap]
    fun_prop
  rw [circleIntegrable_iff]
  refine intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
    (bound := fun θ ↦ |R| * bound (circleMap c R θ)) hs
    (hF_meas.mono fun _ hx ↦ hcont.aestronglyMeasurable.smul hx)
    ((circleIntegrable_iff R).mp hF_int)
    (hcont.aestronglyMeasurable.smul hF'_meas) ?_
    (bound_integrable.const_mul _) ?_
  · apply Filter.Eventually.of_forall
    intro θ _
    have h := (lipschitzWith_smul (deriv (circleMap c R) θ)).comp_lipschitzOnWith
      (h_lipsch _ (circleMap_mem_sphere' c R θ))
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa [mul_assoc] using h.dist_le_mul x hx y hy
  · exact Filter.Eventually.of_forall fun θ _ ↦
      (h_diff _ (circleMap_mem_sphere' c R θ)).const_smul _
