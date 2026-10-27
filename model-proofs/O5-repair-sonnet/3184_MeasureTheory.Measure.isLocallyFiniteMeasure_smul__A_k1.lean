/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.isLocallyFiniteMeasure_smul
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean, line 315
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem Measure.isLocallyFiniteMeasure_smul [TopologicalSpace α] (μ : Measure α)
    [IsLocallyFiniteMeasure μ] {c : ℝ≥0∞} (h : c ≠ ∞) :
    IsLocallyFiniteMeasure (c • μ) := by
  refine ⟨fun x => ?_⟩
  rcases (μ.finiteAt_nhds x) with ⟨s, hs, hμs⟩
  refine ⟨s, hs, ?_⟩
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top h.lt_top hμs
