/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.one_add_pow_mul_norm_fourier_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Fourier/FourierTransformDeriv.lean, line 840
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 0 (round 0 = first attempt)
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
  have hN : ContDiff ℝ ((n : ℕ∞)) f := by exact_mod_cast hf
  have h := Real.fourier_iteratedDeriv (N := (n : ℕ∞)) (n := n) hN
    (fun k hk => h'f k (by exact_mod_cast hk)) le_rfl
  have h1 : ‖𝓕 f u‖ ≤ ∫ v, ‖f v‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  have h2 : ‖𝓕 (iteratedDeriv n f) u‖ ≤ ∫ v, ‖iteratedDeriv n f v‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  have h3 : ‖𝓕 (iteratedDeriv n f) u‖ = (2 * π) ^ n * |u| ^ n * ‖𝓕 f u‖ := by
    have := congrFun h u
    rw [this]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_pi, Complex.norm_I, mul_one]
    ring
  have hp : 0 < (2 * π) ^ n := by positivity
  have h4 : |u| ^ n * ‖𝓕 f u‖ ≤ ((2 * π) ^ n)⁻¹ * ∫ v, ‖iteratedDeriv n f v‖ := by
    rw [← div_eq_inv_mul, le_div_iff₀ hp]
    linarith
  linarith
