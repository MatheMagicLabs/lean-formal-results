/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.one_add_pow_mul_norm_fourier_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Fourier/FourierTransformDeriv.lean, line 840
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
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
  have hf' : ContDiff ℝ (n : ℕ∞) f := by exact_mod_cast hf
  have h'f' : ∀ k : ℕ, k ≤ (n : ℕ∞) → Integrable (iteratedDeriv k f) :=
    fun k hk ↦ h'f k (by exact_mod_cast hk)
  have key : ∀ g : ℝ → E, ‖𝓕 g u‖ ≤ ∫ v, ‖g v‖ := by
    intro g
    rw [fourier_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    simp [Circle.norm_smul]
  have h1 := key f
  have h2 := key (iteratedDeriv n f)
  have h3 : 𝓕 (iteratedDeriv n f) u = (2 * π * I * u) ^ n • (𝓕 f u) := by
    have := fourier_iteratedDeriv (N := (n : ℕ∞)) (n := n) hf' h'f' le_rfl
    exact congrFun this u
  have h5 : ‖𝓕 (iteratedDeriv n f) u‖ = (2 * π) ^ n * (|u| ^ n * ‖𝓕 f u‖) := by
    rw [h3]
    simp [norm_smul, norm_mul, mul_pow, abs_of_pos Real.pi_pos] <;> ring
  have h4 : |u| ^ n * ‖𝓕 f u‖ ≤ ((2 * π) ^ n)⁻¹ * ∫ v, ‖iteratedDeriv n f v‖ := by
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    rw [h5] at h2
    linarith
  have := add_le_add h1 h4
  nlinarith [this]
