/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Metric.image_homothety_ball
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Affine/AddTorsor.lean, line 148
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

noncomputable section
open NNReal
variable {V P W Q : Type*} [SeminormedAddCommGroup V] [PseudoMetricSpace P] [NormedAddTorsor V P]
section NormedSpace
variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] [NormedSpace 𝕜 W]
open AffineMap
open scoped Pointwise in

theorem Metric.image_homothety_ball (p c : P) (r : ℝ) {x : 𝕜} (hx : x ≠ 0) :
    homothety c x '' ball p r = ball (homothety c x p) (‖x‖ * r) := by
  have key : ∀ a b : P, dist (homothety c x a) (homothety c x b) = ‖x‖ * dist a b := by
    intro a b
    rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, homothety_apply, homothety_apply,
      vadd_vsub_vadd_cancel_right, ← smul_sub, vsub_sub_vsub_cancel_right, norm_smul]
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Metric.mem_ball, key]
    rw [Metric.mem_ball] at hz
    exact mul_lt_mul_of_pos_left hz (norm_pos_iff.2 hx)
  · intro hy
    have hy' : homothety c x (homothety c x⁻¹ y) = y := by
      rw [← homothety_mul_apply, mul_inv_cancel₀ hx, homothety_one, AffineMap.id_apply]
    refine ⟨homothety c x⁻¹ y, ?_, hy'⟩
    rw [Metric.mem_ball] at hy ⊢
    rw [← hy', key] at hy
    exact lt_of_mul_lt_mul_left hy (norm_nonneg x)
