/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Metric.image_homothety_closedBall
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Affine/AddTorsor.lean, line 153
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  have hd (a b : P) :
      dist (homothety c x a) (homothety c x b) = ‖x‖ * dist a b := by
    simp only [homothety_apply, dist_vadd_cancel_right]
    rw [dist_eq_norm, ← smul_sub, norm_smul, ← dist_eq_norm,
      dist_vsub_cancel_right]
  ext q
  constructor
  · rintro ⟨a, ha, rfl⟩
    change dist a p ≤ r at ha
    change dist (homothety c x a) (homothety c x p) ≤ ‖x‖ * r
    rw [hd]
    exact mul_le_mul_of_nonneg_left ha (norm_nonneg x)
  · intro hq
    have hi : homothety c x (homothety c x⁻¹ q) = q := by
      simp [homothety_apply, smul_smul, hx]
    refine ⟨homothety c x⁻¹ q, ?_, hi⟩
    change dist (homothety c x⁻¹ q) p ≤ r
    have h : ‖x‖ * dist (homothety c x⁻¹ q) p ≤ ‖x‖ * r := by
      rw [← hd, hi]
      exact hq
    have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
    nlinarith
