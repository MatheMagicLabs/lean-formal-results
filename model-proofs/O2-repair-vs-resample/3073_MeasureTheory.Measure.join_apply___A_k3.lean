/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.join_apply₀
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/GiryMonad.lean, line 171
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem join_apply₀ {m : Measure (Measure α)} {s : Set α} (hs : NullMeasurableSet s m.join) :
    join m s = ∫⁻ μ, μ s ∂m := by
  obtain ⟨t, hst, htm, hts⟩ := hs.exists_measurable_superset_ae_eq
  rw [← measure_congr hts, join_apply htm]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_ae_of_ae_join hts] with μ hμ
  exact measure_congr hμ
