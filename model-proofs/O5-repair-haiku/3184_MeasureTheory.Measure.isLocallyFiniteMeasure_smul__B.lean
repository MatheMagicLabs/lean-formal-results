/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.isLocallyFiniteMeasure_smul
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean, line 315
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-haiku, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-haiku-4-5
Setup:       Haiku 4.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem Measure.isLocallyFiniteMeasure_smul [TopologicalSpace α] (μ : Measure α)
    [IsLocallyFiniteMeasure μ] {c : ℝ≥0∞} (h : c ≠ ∞) :
    IsLocallyFiniteMeasure (c • μ) := by
  constructor
  intro x
  obtain ⟨s, hs_mem, hs_finite⟩ := μ.finiteAt_nhds x
  exact ⟨s, hs_mem, by simpa using ENNReal.mul_lt_top (by exact_mod_cast h.lt_top) hs_finite⟩
