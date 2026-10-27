/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.bind_map
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/GiryMonad.lean, line 334
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem bind_map {γ} [MeasurableSpace γ] {m : Measure α} {f : α → β} {g : β → Measure γ}
    (hf : AEMeasurable f m) (hg : AEMeasurable g (m.map f)) :
    bind (map f m) g = bind m fun a ↦ g (f a) := by
  ext1 s hs
  rw [bind_apply hs hg, bind_apply (f := fun a ↦ g (f a)) hs (hg.comp_aemeasurable hf),
    lintegral_map' (f := fun b ↦ g b s) ((measurable_coe hs).comp_aemeasurable hg) hf]
