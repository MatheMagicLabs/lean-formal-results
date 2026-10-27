/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.setLIntegral_congr_fun_ae₀
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean, line 284
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem setLIntegral_congr_fun_ae₀ {f g : α → ℝ≥0∞} {s : Set α} (hs : NullMeasurableSet s μ)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → f x = g x) : ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ := by
  exact lintegral_congr_ae ((ae_restrict_iff'₀ hs).2 hfg)
