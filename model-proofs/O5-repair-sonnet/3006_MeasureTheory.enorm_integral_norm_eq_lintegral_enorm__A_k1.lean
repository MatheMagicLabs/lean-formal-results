/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.enorm_integral_norm_eq_lintegral_enorm
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Integral/Bochner/Basic.lean, line 548
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem enorm_integral_norm_eq_lintegral_enorm {P : Type*} [NormedAddCommGroup P] {f : α → P}
    (hf : Integrable f μ) : ‖∫ x, ‖f x‖ ∂μ‖ₑ = ∫⁻ x, ‖f x‖ₑ ∂μ := by
  rw [integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable, ← ofReal_norm,
    Real.norm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal]
  exact lt_top_iff_ne_top.mp (hasFiniteIntegral_iff_enorm.mpr hf.2)
