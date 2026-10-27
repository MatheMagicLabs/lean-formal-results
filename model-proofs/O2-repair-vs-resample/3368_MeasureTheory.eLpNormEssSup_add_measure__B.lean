/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.eLpNormEssSup_add_measure
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean, line 972
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma eLpNormEssSup_add_measure {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε} :
    eLpNormEssSup f (μ + ν) = max (eLpNormEssSup f μ) (eLpNormEssSup f ν) := by
  apply le_antisymm
  · apply eLpNormEssSup_le_of_ae_enorm_bound
    rw [ae_add_measure_iff]
    exact ⟨(ae_le_eLpNormEssSup (f := f) (μ := μ)).mono fun x hx => hx.trans (le_max_left _ _),
      (ae_le_eLpNormEssSup (f := f) (μ := ν)).mono fun x hx => hx.trans (le_max_right _ _)⟩
  · exact max_le
      (eLpNormEssSup_mono_measure f
        (Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)))
      (eLpNormEssSup_mono_measure f
        (Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)))
