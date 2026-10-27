/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Metric.image_homothety_closedBall_of_nonneg
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Affine/AddTorsor.lean, line 159
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

theorem Metric.image_homothety_closedBall_of_nonneg (p c : Q) {r : ℝ} (hr : 0 ≤ r) (x : 𝕜) :
    homothety c x '' closedBall p r = closedBall (homothety c x p) (‖x‖ * r) := by
  have hd : ∀ a b : Q,
      dist (homothety c x a) (homothety c x b) = ‖x‖ * dist a b := by
    intro a b
    simp [homothety_def, dist_eq_norm_vsub, ← smul_sub, norm_smul]
  apply Set.Subset.antisymm
  · rintro y ⟨q, hq, rfl⟩
    change dist (homothety c x q) (homothety c x p) ≤ ‖x‖ * r
    rw [hd]
    exact mul_le_mul_of_nonneg_left hq (norm_nonneg x)
  · intro y hy
    change dist y (homothety c x p) ≤ ‖x‖ * r at hy
    by_cases hx : x = 0
    · have hyc : y = c := by
        simpa [hx, homothety_def] using hy
      subst y
      refine ⟨p, ?_, ?_⟩
      · simpa using hr
      · simp [hx, homothety_def]
    · have hi : ∀ z : Q, homothety c x (homothety c x⁻¹ z) = z := by
        intro z
        simp [homothety_def, smul_smul, hx]
      refine ⟨homothety c x⁻¹ y, ?_, hi y⟩
      change dist (homothety c x⁻¹ y) p ≤ r
      have hmul : ‖x‖ * dist (homothety c x⁻¹ y) p ≤ ‖x‖ * r := by
        rw [← hd, hi]
        exact hy
      have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      nlinarith
