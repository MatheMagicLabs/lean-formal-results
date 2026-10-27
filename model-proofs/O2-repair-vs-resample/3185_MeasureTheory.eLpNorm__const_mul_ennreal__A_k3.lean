/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.eLpNorm'_const_mul_ennreal
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/SMul.lean, line 149
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem eLpNorm'_const_mul_ennreal {f : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hq_pos : 0 < q) (hf : AEStronglyMeasurable f μ) :
    eLpNorm' (fun x ↦ c * f x) q μ = c * eLpNorm' f q μ := by
  simp only [eLpNorm'_eq_lintegral_enorm, enorm_eq_self]
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hq_pos.le]
  rw [lintegral_const_mul'' _ (hf.aemeasurable.pow_const q),
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hq_pos.le), one_div,
    ENNReal.rpow_rpow_inv hq_pos.ne']
