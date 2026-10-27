/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Metric.image_homothety_closedBall
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Affine/AddTorsor.lean, line 153
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

theorem Metric.image_homothety_closedBall (p c : P) (r : ℝ) {x : 𝕜} (hx : x ≠ 0) :
    homothety c x '' closedBall p r = closedBall (homothety c x p) (‖x‖ * r) := by
  have key : ∀ z, dist (homothety c x z) (homothety c x p) = ‖x‖ * dist z p := by
    intro z
    rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, homothety_apply, homothety_apply,
      vadd_vsub_vadd_cancel_right, ← smul_sub, vsub_sub_vsub_cancel_right, norm_smul]
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Metric.mem_closedBall, key]
    exact mul_le_mul_of_nonneg_left (Metric.mem_closedBall.1 hz) (norm_nonneg _)
  · intro hy
    have hyz : homothety c x (homothety c x⁻¹ y) = y := by
      rw [← homothety_mul_apply, mul_inv_cancel₀ hx]
      simp
    refine ⟨homothety c x⁻¹ y, ?_, hyz⟩
    rw [Metric.mem_closedBall]
    have h := Metric.mem_closedBall.1 hy
    rw [← hyz, key] at h
    exact le_of_mul_le_mul_left h (norm_pos_iff.2 hx)
