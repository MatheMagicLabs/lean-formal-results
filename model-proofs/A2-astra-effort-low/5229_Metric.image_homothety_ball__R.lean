/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Metric.image_homothety_ball
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Affine/AddTorsor.lean, line 148
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
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
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hd (a b : P) :
      dist (homothety c x a) (homothety c x b) = ‖x‖ * dist a b := by
    simp [homothety_apply, dist_eq_norm_vsub V, ← smul_sub, norm_smul]
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [Metric.mem_ball] at ha ⊢
    rw [hd]
    have h := mul_pos hpos (sub_pos.mpr ha)
    nlinarith
  · intro hy
    rw [Metric.mem_ball] at hy
    have he : homothety c x (homothety c x⁻¹ y) = y := by
      simp [homothety_apply, smul_smul, hx]
    refine ⟨homothety c x⁻¹ y, ?_, he⟩
    rw [Metric.mem_ball]
    have h :
        dist (homothety c x (homothety c x⁻¹ y)) (homothety c x p) <
          ‖x‖ * r := by
      simpa only [he] using hy
    rw [hd] at h
    by_contra hn
    have hnonneg := mul_nonneg (le_of_lt hpos)
      (sub_nonneg.mpr (le_of_not_gt hn))
    nlinarith
