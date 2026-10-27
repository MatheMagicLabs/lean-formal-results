/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.one_add_pow_mul_norm_fourier_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Fourier/FourierTransformDeriv.lean, line 840
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
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
  have key (g : ℝ → E) (w : ℝ) : ‖𝓕 g w‖ ≤ ∫ v, ‖g v‖ := by
    rw [fourier_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr with v
    simp [Circle.norm_smul]
  have h1 := key f u
  have h2 := key (iteratedDeriv n f) u
  rw [fourier_iteratedDeriv (N := (n : ℕ∞)) (by exact_mod_cast hf)
    (fun k hk => h'f k (by exact_mod_cast hk)) le_rfl] at h2
  have hp : 0 < (2 * π) ^ n := by positivity
  have h3 : |u| ^ n * ‖𝓕 f u‖ ≤ ((2 * π) ^ n)⁻¹ * ∫ v, ‖iteratedDeriv n f v‖ := by
    rw [le_inv_mul_iff₀ hp]
    calc (2 * π) ^ n * (|u| ^ n * ‖𝓕 f u‖)
        = ‖(2 * π * I * u) ^ n • 𝓕 f u‖ := by
          simp [norm_smul, mul_pow, abs_pi, Complex.norm_real] <;> ring
      _ ≤ _ := h2
  calc (1 + |u| ^ n) * ‖𝓕 f u‖ = ‖𝓕 f u‖ + |u| ^ n * ‖𝓕 f u‖ := by ring
    _ ≤ _ := add_le_add h1 h3
