/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Metric.image_homothety_ball
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Affine/AddTorsor.lean, line 148
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

theorem Metric.image_homothety_ball (p c : P) (r : ℝ) {x : 𝕜} (hx : x ≠ 0) :
    homothety c x '' ball p r = ball (homothety c x p) (‖x‖ * r) := by
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hd (a b : P) :
      dist (homothety c x a) (homothety c x b) = ‖x‖ * dist a b := by
    simp [homothety_apply, dist_eq_norm_vsub V, ← smul_sub, norm_smul]
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change dist (homothety c x z) (homothety c x p) < ‖x‖ * r
    rw [hd]
    exact mul_lt_mul_of_pos_left hz hx'
  · intro hy
    have hc : homothety c x (homothety c x⁻¹ y) = y := by
      simp [homothety_apply, smul_smul, hx]
    refine ⟨homothety c x⁻¹ y, ?_, hc⟩
    change dist (homothety c x⁻¹ y) p < r
    have h : ‖x‖ * dist (homothety c x⁻¹ y) p < ‖x‖ * r := by
      rw [← hd, hc]
      exact hy
    by_contra hn
    have hge : r ≤ dist (homothety c x⁻¹ y) p := le_of_not_gt hn
    have hmul := mul_le_mul_of_nonneg_left hge (le_of_lt hx')
    exact (not_lt_of_ge hmul) h
