/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Metric.image_homothety_ball
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Affine/AddTorsor.lean, line 148
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have happly (a : P) :
      homothety c x a = x • (a -ᵥ c) +ᵥ c := by
    rfl
  have hd (a b : P) :
      dist (homothety c x a) (homothety c x b) = ‖x‖ * dist a b := by
    simp only [happly, dist_eq_norm_vsub V,
      vadd_vsub_vadd_cancel_right, ← smul_sub,
      vsub_sub_vsub_cancel_right, norm_smul]
  ext q
  constructor
  · rintro ⟨a, ha, rfl⟩
    change dist (homothety c x a) (homothety c x p) < ‖x‖ * r
    rw [hd]
    exact mul_lt_mul_of_pos_left ha hxpos
  · intro hq
    let a : P := x⁻¹ • (q -ᵥ c) +ᵥ c
    have ha : homothety c x a = q := by
      rw [happly]
      dsimp [a]
      simp [smul_smul, hx]
    refine ⟨a, ?_, ha⟩
    change dist a p < r
    have h : ‖x‖ * dist a p < ‖x‖ * r := by
      rw [← hd, ha]
      exact hq
    nlinarith
