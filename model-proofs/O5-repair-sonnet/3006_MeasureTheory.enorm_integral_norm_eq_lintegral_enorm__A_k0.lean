/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.enorm_integral_norm_eq_lintegral_enorm
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Integral/Bochner/Basic.lean, line 548
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem enorm_integral_norm_eq_lintegral_enorm {P : Type*} [NormedAddCommGroup P] {f : α → P}
    (hf : Integrable f μ) : ‖∫ x, ‖f x‖ ∂μ‖ₑ = ∫⁻ x, ‖f x‖ₑ ∂μ := by
  have h0 : 0 ≤ ∫ x, ‖f x‖ ∂μ := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => by simp) hf.aestronglyMeasurable.norm]
    exact ENNReal.toReal_nonneg
  rw [← ofReal_integral_norm_eq_lintegral_enorm hf]
  first
    | exact Real.enorm_of_nonneg h0
    | exact Real.enorm_eq_ofReal h0
