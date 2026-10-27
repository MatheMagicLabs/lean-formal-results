/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Metric.image_homothety_sphere_of_nonneg
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Affine/AddTorsor.lean, line 170
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm N1, verified in round 0 (round 0 = first attempt)
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

theorem Metric.image_homothety_sphere_of_nonneg [NormedSpace ℝ W] [Nontrivial W]
    (p c : Q) {r : ℝ} (hr : 0 ≤ r) (x : 𝕜) :
    homothety c x '' sphere p r = sphere (homothety c x p) (‖x‖ * r) := by
  have hs : (sphere p r).Nonempty := by
    obtain ⟨v, hv⟩ := exists_ne (0 : W)
    refine ⟨(r / ‖v‖) • v +ᵥ p, ?_⟩
    simpa [Metric.mem_sphere, dist_eq_norm_vsub, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr (norm_nonneg v)),
      norm_ne_zero_iff.mpr hv]
  by_cases hx : x = 0
  · subst x
    ext q
    simp only [Set.mem_image, homothety_def, zero_smul, zero_vadd,
      norm_zero, zero_mul, Metric.mem_sphere, dist_eq_zero]
    constructor
    · rintro ⟨a, ha, h⟩
      exact h.symm
    · intro h
      exact ⟨hs.choose, hs.choose_spec, h.symm⟩
  · have hd : ∀ a b : Q,
        dist (homothety c x a) (homothety c x b) = ‖x‖ * dist a b := by
      intro a b
      simp [homothety_def, dist_eq_norm_vsub, ← smul_sub,
        vsub_sub_vsub_cancel_right, norm_smul]
    have hi : ∀ q : Q, homothety c x (homothety c x⁻¹ q) = q := by
      intro q
      simp [homothety_def, smul_smul, hx]
    ext q
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [Metric.mem_sphere] at ha ⊢
      rw [hd, ha]
    · intro hq
      refine ⟨homothety c x⁻¹ q, ?_, hi q⟩
      rw [Metric.mem_sphere] at hq ⊢
      apply mul_left_cancel₀ (norm_ne_zero_iff.mpr hx)
      rw [← hd, hi]
      exact hq
