/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.bind_apply₀
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/GiryMonad.lean, line 257
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem bind_apply₀ {m : Measure α} {f : α → Measure β} {s : Set β}
    (hs : NullMeasurableSet s (m.bind f)) (hf : AEMeasurable f m) :
    bind m f s = ∫⁻ a, f a s ∂m := by
  obtain ⟨t, -, ht, hst⟩ := hs.exists_measurable_superset_ae_eq
  rw [← measure_congr hst, bind_apply ht hf]
  have h := ae_ae_of_ae_bind (p := fun x => t x = s x) hf hst
  exact lintegral_congr_ae (h.mono fun a ha => measure_congr ha)
