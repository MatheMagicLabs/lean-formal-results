/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.one_add_pow_mul_norm_fourier_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Fourier/FourierTransformDeriv.lean, line 840
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
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
  have H1 : ∀ g : ℝ → E, ∀ u : ℝ, ‖𝓕 g u‖ ≤ ∫ v, ‖g v‖ := by
    intro g u
    rw [fourier_real_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr with v
    simp [Circle.norm_smul]
  have key : (2 * π) ^ n * (|u| ^ n * ‖𝓕 f u‖) ≤ ∫ v, ‖iteratedDeriv n f v‖ := by
    have := H1 (iteratedDeriv n f) u
    rw [fourier_iteratedDeriv (N := (n : ℕ∞)) (by exact_mod_cast hf)
      (fun k hk => h'f k (by exact_mod_cast hk)) le_rfl] at this
    convert this using 1
    simp [norm_smul, mul_pow, abs_of_pos pi_pos]
    try ring
  have hpos : 0 < (2 * π) ^ n := by positivity
  calc (1 + |u| ^ n) * ‖𝓕 f u‖
      = ‖𝓕 f u‖ + ((2 * π) ^ n)⁻¹ * ((2 * π) ^ n * (|u| ^ n * ‖𝓕 f u‖)) := by
        rw [inv_mul_cancel_left₀ hpos.ne']; ring
    _ ≤ (∫ v, ‖f v‖) + ((2 * π) ^ n)⁻¹ * ∫ v, ‖iteratedDeriv n f v‖ :=
        add_le_add (H1 f u) (mul_le_mul_of_nonneg_left key (by positivity))
