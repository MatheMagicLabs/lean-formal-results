/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Metric.image_homothety_closedBall_of_nonneg
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Affine/AddTorsor.lean, line 159
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
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

theorem Metric.image_homothety_closedBall_of_nonneg (p c : Q) {r : ℝ} (hr : 0 ≤ r) (x : 𝕜) :
    homothety c x '' closedBall p r = closedBall (homothety c x p) (‖x‖ * r) := by
  rcases eq_or_ne x 0 with rfl | hx
  · have hne : (closedBall p r).Nonempty := Metric.nonempty_closedBall.2 hr
    simp only [homothety_zero, norm_zero, zero_mul, closedBall_zero, coe_const]
    first
      | exact hne.image_const c
      | simp [hne.image_const]
  · have key : ∀ y : Q, homothety c x (homothety c x⁻¹ y) = y := by
      intro y
      rw [← homothety_mul_apply, mul_inv_cancel₀ hx, homothety_one, AffineMap.id_apply]
    have hd : ∀ a b : Q, dist (homothety c x a) (homothety c x b) = ‖x‖ * dist a b := by
      intro a b
      rw [homothety_apply, homothety_apply, dist_vadd_cancel_right, dist_smul₀,
        dist_vsub_cancel_right]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [mem_closedBall] at hz ⊢
      rw [hd]
      exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)
    · intro hy
      refine ⟨homothety c x⁻¹ y, ?_, key y⟩
      rw [mem_closedBall] at hy ⊢
      have h2 := hd (homothety c x⁻¹ y) p
      rw [key y] at h2
      rw [h2] at hy
      exact le_of_mul_le_mul_left hy (norm_pos_iff.2 hx)
