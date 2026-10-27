/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.isLocallyFiniteMeasure_smul
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean, line 315
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem Measure.isLocallyFiniteMeasure_smul [TopologicalSpace α] (μ : Measure α)
    [IsLocallyFiniteMeasure μ] {c : ℝ≥0∞} (h : c ≠ ∞) :
    IsLocallyFiniteMeasure (c • μ) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨s, hxs, hs, hμs⟩ := μ.exists_isOpen_measure_lt_top x
  refine ⟨s, hs.mem_nhds hxs, ?_⟩
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top h.lt_top hμs
