/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Metric.image_homothety_ball
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Affine/AddTorsor.lean, line 148
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem Metric.image_homothety_ball (p c : P) (r : ℝ) {x : 𝕜} (hx : x ≠ 0) :
    homothety c x '' ball p r = ball (homothety c x p) (‖x‖ * r) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_ball] at hz ⊢
    rw [dist_homothety]
    exact mul_lt_mul_of_pos_left hz (norm_pos_iff.2 hx)
  · intro hy
    have hw : homothety c x (homothety c x⁻¹ y) = y := by
      simp [homothety_apply, smul_smul, hx]
    refine ⟨homothety c x⁻¹ y, ?_, hw⟩
    rw [mem_ball] at hy ⊢
    rw [← hw, dist_homothety] at hy
    exact lt_of_mul_lt_mul_left hy (norm_nonneg _)
