/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.integrable_indicator_iff₀
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Integral/IntegrableOn.lean, line 334
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem integrable_indicator_iff₀ (hs : NullMeasurableSet s μ) :
    Integrable (indicator s f) μ ↔ IntegrableOn f s μ := by
  obtain ⟨t, hst, ht, hts⟩ := hs.exists_measurable_superset_ae_eq
  have h1 : indicator s f =ᵐ[μ] indicator t f := indicator_ae_eq_of_ae_eq_set hts.symm
  rw [integrable_congr h1, integrableOn_congr_set_ae hts.symm]
  first
    | (rw [IntegrableOn, ← memLp_one_iff_integrable, ← memLp_one_iff_integrable,
        memLp_indicator_iff_restrict ht])
    | (simp [IntegrableOn, Integrable, HasFiniteIntegral, enorm_indicator_eq_indicator_enorm,
        lintegral_indicator ht, aestronglyMeasurable_indicator_iff ht])
