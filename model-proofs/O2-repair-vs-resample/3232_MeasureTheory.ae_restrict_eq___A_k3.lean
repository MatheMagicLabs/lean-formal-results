/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.ae_restrict_eq₀
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/Restrict.lean, line 697
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem ae_restrict_eq₀ (hs : NullMeasurableSet s μ) : ae (μ.restrict s) = ae μ ⊓ 𝓟 s := by
  refine le_antisymm ?_ le_ae_restrict
  intro t ht
  rw [mem_inf_principal] at ht
  exact (ae_restrict_iff'₀ (p := fun x => x ∈ t) hs).2 ht
