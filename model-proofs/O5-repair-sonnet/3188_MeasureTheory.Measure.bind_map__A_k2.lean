/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.bind_map
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/GiryMonad.lean, line 334
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem bind_map {γ} [MeasurableSpace γ] {m : Measure α} {f : α → β} {g : β → Measure γ}
    (hf : AEMeasurable f m) (hg : AEMeasurable g (m.map f)) :
    bind (map f m) g = bind m fun a ↦ g (f a) := by
  ext1 s hs
  rw [bind_apply hs hg,
    bind_apply hs (f := fun a => g (f a)) (hg.comp_aemeasurable hf : AEMeasurable (fun a => g (f a)) m)]
  exact lintegral_map' ((measurable_coe hs).comp_aemeasurable hg) hf
