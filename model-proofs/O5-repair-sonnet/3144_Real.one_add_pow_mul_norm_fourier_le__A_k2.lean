/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.one_add_pow_mul_norm_fourier_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Fourier/FourierTransformDeriv.lean, line 840
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem one_add_pow_mul_norm_fourier_le {f : ℝ → E} {n : ℕ} (hf : ContDiff ℝ n f)
    (h'f : ∀ k ≤ n, Integrable (iteratedDeriv k f)) (u : ℝ) :
    (1 + |u| ^ n) * ‖𝓕 f u‖ ≤
      (∫ v, ‖f v‖) + ((2 * π) ^ n)⁻¹ * ∫ v, ‖iteratedDeriv n f v‖ := by
  have key : ∀ g : ℝ → E, ‖𝓕 g u‖ ≤ ∫ v, ‖g v‖ := by
    intro g
    first
      | exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
      | (rw [fourier_eq]
         refine (norm_integral_le_integral_norm _).trans_eq ?_
         congr 1
         ext v
         exact Circle.norm_smul _ _)
  have hf' : ContDiff ℝ ((n : ℕ∞) : ℕ∞ω) f := by exact_mod_cast hf
  have h'f' : ∀ k : ℕ, k ≤ (n : ℕ∞) → Integrable (iteratedDeriv k f) := by
    intro k hk
    exact h'f k (by exact_mod_cast hk)
  have h1 : ‖𝓕 f u‖ ≤ ∫ v, ‖f v‖ := key f
  have h2 : ‖𝓕 (iteratedDeriv n f) u‖ = (2 * π) ^ n * |u| ^ n * ‖𝓕 f u‖ := by
    rw [fourier_iteratedDeriv hf' h'f' (le_refl _)]
    simp [norm_smul, mul_pow]
  have h3 : (2 * π) ^ n * |u| ^ n * ‖𝓕 f u‖ ≤ ∫ v, ‖iteratedDeriv n f v‖ := by
    rw [← h2]
    exact key _
  have h4 : |u| ^ n * ‖𝓕 f u‖ ≤ ((2 * π) ^ n)⁻¹ * ∫ v, ‖iteratedDeriv n f v‖ := by
    have hp : 0 < (2 * π) ^ n := by positivity
    rw [← div_eq_inv_mul, le_div_iff₀ hp]
    nlinarith [h3]
  nlinarith [h1, h4]
