/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.one_add_pow_mul_norm_fourier_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Fourier/FourierTransformDeriv.lean, line 840
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
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
    rw [Real.fourier_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    simp [Circle.norm_smul]
  have h1 := key f
  have h2 := fourier_iteratedDeriv (N := (n : ℕ∞)) (n := n) (mod_cast hf)
    (fun k hk => h'f k (mod_cast hk)) le_rfl
  have h3 := key (iteratedDeriv n f)
  rw [h2] at h3
  have hn : ‖(2 * (π : ℂ) * I * (u : ℂ))‖ = 2 * π * |u| := by
    simp [norm_mul, abs_pi]
  simp only [norm_smul, norm_pow, hn] at h3
  have h4 : |u| ^ n * ‖𝓕 f u‖ ≤ ((2 * π) ^ n)⁻¹ * ∫ v, ‖iteratedDeriv n f v‖ := by
    rw [← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    rw [mul_pow] at h3
    have : |u| ^ n * ‖𝓕 f u‖ * (2 * π) ^ n = (2 * π) ^ n * |u| ^ n * ‖𝓕 f u‖ := by ring
    linarith
  have h5 : (1 + |u| ^ n) * ‖𝓕 f u‖ = ‖𝓕 f u‖ + |u| ^ n * ‖𝓕 f u‖ := by ring
  linarith
