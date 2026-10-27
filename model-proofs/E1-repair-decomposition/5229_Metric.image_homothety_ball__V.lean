/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Metric.image_homothety_ball
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Affine/AddTorsor.lean, line 148
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
  have hd (a b : P) :
      dist (homothety c x a) (homothety c x b) = ‖x‖ * dist a b := by
    simp only [dist_eq_norm_vsub V]
    change ‖(x • (a -ᵥ c) +ᵥ c) -ᵥ (x • (b -ᵥ c) +ᵥ c)‖ =
      ‖x‖ * ‖a -ᵥ b‖
    rw [vadd_vsub_vadd_cancel_right, ← smul_sub,
      vsub_sub_vsub_cancel_right, norm_smul]
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change dist z p < r at hz
    change dist (homothety c x z) (homothety c x p) < ‖x‖ * r
    rw [hd]
    have h := mul_pos hx' (sub_pos.mpr hz)
    nlinarith
  · intro hy
    have hi : homothety c x (homothety c x⁻¹ y) = y := by
      change x • ((x⁻¹ • (y -ᵥ c) +ᵥ c) -ᵥ c) +ᵥ c = y
      simp [smul_smul, hx]
    refine ⟨homothety c x⁻¹ y, ?_, hi⟩
    change dist (homothety c x⁻¹ y) p < r
    change dist y (homothety c x p) < ‖x‖ * r at hy
    have hdist := hd (homothety c x⁻¹ y) p
    rw [hi] at hdist
    rw [hdist] at hy
    by_contra hn
    have h := mul_nonneg (le_of_lt hx')
      (sub_nonneg.mpr (le_of_not_gt hn))
    nlinarith
