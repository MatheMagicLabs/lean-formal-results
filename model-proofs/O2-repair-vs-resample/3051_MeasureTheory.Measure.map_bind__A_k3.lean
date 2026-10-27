/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.map_bind
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/GiryMonad.lean, line 325
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem map_bind {γ} [MeasurableSpace γ] {m : Measure α} {f : α → Measure β} {g : β → γ}
    (hf : AEMeasurable f m) (hg : AEMeasurable g (m.bind f)) :
    map g (bind m f) = bind m fun a ↦ map g (f a) := by
  ext1 s hs
  have hf' : AEMeasurable (fun a ↦ map g (f a)) m :=
    (aemeasurable_map (m := map f m) hg).comp_aemeasurable hf
  rw [map_apply_of_aemeasurable hg hs, bind_apply₀ (hg.nullMeasurable hs) hf,
    bind_apply hs hf']
  exact lintegral_congr_ae <| (hf.ae_of_bind hg).mono fun a ha ↦
    (map_apply_of_aemeasurable ha hs).symm
