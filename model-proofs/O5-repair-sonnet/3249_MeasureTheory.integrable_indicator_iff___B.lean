/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.integrable_indicator_iff₀
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Integral/IntegrableOn.lean, line 334
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem integrable_indicator_iff₀ (hs : NullMeasurableSet s μ) :
    Integrable (indicator s f) μ ↔ IntegrableOn f s μ := by
  simp [IntegrableOn, Integrable, HasFiniteIntegral, enorm_indicator_eq_indicator_enorm,
    lintegral_indicator₀ hs, aestronglyMeasurable_indicator_iff₀ hs]
