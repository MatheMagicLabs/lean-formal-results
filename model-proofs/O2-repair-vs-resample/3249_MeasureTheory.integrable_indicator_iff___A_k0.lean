/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.integrable_indicator_iff₀
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Integral/IntegrableOn.lean, line 334
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem integrable_indicator_iff₀ (hs : NullMeasurableSet s μ) :
    Integrable (indicator s f) μ ↔ IntegrableOn f s μ := by
  have ht := measurableSet_toMeasurable μ s
  have hst : toMeasurable μ s =ᵐ[μ] s := hs.toMeasurable_ae_eq
  rw [integrable_congr (indicator_ae_eq_of_ae_eq_set hst.symm),
    ← integrableOn_congr_set_ae hst]
  simp_rw [IntegrableOn, Integrable, HasFiniteIntegral,
    enorm_indicator_eq_indicator_enorm, lintegral_indicator ht,
    aestronglyMeasurable_indicator_iff ht]
