/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.one_add_pow_mul_norm_fourier_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Fourier/FourierTransformDeriv.lean, line 840
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
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
    rw [fourier_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr with v
    first | exact Circle.norm_smul _ _ | simp
  have h1 := key f
  have e : ‖(2 * π * I * (u : ℂ)) ^ n • 𝓕 f u‖ = (2 * π) ^ n * (|u| ^ n * ‖𝓕 f u‖) := by
    simp only [norm_smul, norm_pow, norm_mul, norm_I, Complex.norm_real, Complex.norm_ofNat,
      Real.norm_eq_abs, abs_of_pos pi_pos, mul_one]
    ring
  have h2 : (2 * π) ^ n * (|u| ^ n * ‖𝓕 f u‖) ≤ ∫ v, ‖iteratedDeriv n f v‖ := by
    rw [← e]
    have := key (iteratedDeriv n f)
    rwa [fourier_iteratedDeriv (N := n) (by exact_mod_cast hf)
      (fun k hk => h'f k (by exact_mod_cast hk)) le_rfl] at this
  have hp : 0 < (2 * π) ^ n := by positivity
  have h3 : |u| ^ n * ‖𝓕 f u‖ ≤ ((2 * π) ^ n)⁻¹ * ∫ v, ‖iteratedDeriv n f v‖ := by
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀' hp).2 h2
  rw [add_mul, one_mul]
  linarith
