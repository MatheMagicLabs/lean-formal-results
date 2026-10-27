/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Metric.image_homothety_sphere_of_nonneg
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Affine/AddTorsor.lean, line 170
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
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

theorem Metric.image_homothety_sphere_of_nonneg [NormedSpace ℝ W] [Nontrivial W]
    (p c : Q) {r : ℝ} (hr : 0 ≤ r) (x : 𝕜) :
    homothety c x '' sphere p r = sphere (homothety c x p) (‖x‖ * r) := by
  by_cases hx : x = 0
  · subst hx
    obtain ⟨v, hv⟩ := exists_norm_eq W hr
    have hne : (sphere p r).Nonempty := ⟨v +ᵥ p, by rw [mem_sphere, dist_vadd_left, hv]⟩
    simp only [homothety_zero, norm_zero, zero_mul, sphere_zero, AffineMap.const_apply,
      AffineMap.coe_const]
    exact hne.image_const c
  · have hd : ∀ a b : Q, dist (homothety c x a) (homothety c x b) = ‖x‖ * dist a b := by
      intro a b
      simp only [homothety_apply, dist_eq_norm_vsub W, vadd_vsub_vadd_cancel_right,
        ← smul_sub, vsub_sub_vsub_cancel_right, norm_smul]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [mem_sphere] at hz ⊢
      rw [hd, hz]
    · intro hy
      rw [mem_sphere] at hy
      have hinv : homothety c x (homothety c x⁻¹ y) = y := by
        rw [← homothety_mul_apply, mul_inv_cancel₀ hx, homothety_one, AffineMap.id_apply]
      refine ⟨homothety c x⁻¹ y, ?_, hinv⟩
      rw [mem_sphere]
      have h1 := hd (homothety c x⁻¹ y) p
      rw [hinv, hy] at h1
      exact (mul_left_cancel₀ (norm_ne_zero_iff.mpr hx) h1).symm
