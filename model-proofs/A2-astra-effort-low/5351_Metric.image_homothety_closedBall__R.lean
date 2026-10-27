/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Metric.image_homothety_closedBall
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Affine/AddTorsor.lean, line 153
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

theorem Metric.image_homothety_closedBall (p c : P) (r : ℝ) {x : 𝕜} (hx : x ≠ 0) :
    homothety c x '' closedBall p r = closedBall (homothety c x p) (‖x‖ * r) := by
  have hdist (a b : P) :
      dist (homothety c x a) (homothety c x b) = ‖x‖ * dist a b := by
    simp only [dist_eq_norm_vsub V]
    change ‖(x • (a -ᵥ c) +ᵥ c) -ᵥ (x • (b -ᵥ c) +ᵥ c)‖ =
      ‖x‖ * ‖a -ᵥ b‖
    rw [vadd_vsub_vadd_cancel_right, ← smul_sub,
      vsub_sub_vsub_cancel_right, norm_smul]
  ext q
  constructor
  · rintro ⟨a, ha, rfl⟩
    change dist (homothety c x a) (homothety c x p) ≤ ‖x‖ * r
    rw [hdist]
    exact mul_le_mul_of_nonneg_left ha (norm_nonneg x)
  · intro hq
    let a : P := x⁻¹ • (q -ᵥ c) +ᵥ c
    have ha : homothety c x a = q := by
      change x • ((x⁻¹ • (q -ᵥ c) +ᵥ c) -ᵥ c) +ᵥ c = q
      simp [smul_smul, hx]
    refine ⟨a, ?_, ha⟩
    change dist a p ≤ r
    have hle : ‖x‖ * dist a p ≤ ‖x‖ * r := by
      rw [← hdist, ha]
      exact hq
    have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    nlinarith
