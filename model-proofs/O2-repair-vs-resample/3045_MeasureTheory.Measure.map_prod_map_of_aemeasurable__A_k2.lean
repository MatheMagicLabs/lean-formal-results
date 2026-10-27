/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.map_prod_map_of_aemeasurable
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/Prod.lean, line 842
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem map_prod_map_of_aemeasurable {δ} [MeasurableSpace δ] {f : α → β} {g : γ → δ}
    (μa : Measure α) (μc : Measure γ) [SFinite μc] (hf : AEMeasurable f μa)
    (hg : AEMeasurable g μc) :
    (map f μa).prod (map g μc) = map (Prod.map f g) (μa.prod μc) := by
  ext s hs
  rw [prod_apply hs,
    lintegral_map' ((measurable_measure_prodMk_left (ν := map g μc) hs).aemeasurable) hf,
    map_apply_of_aemeasurable (hf.prodMap hg) hs,
    prod_apply₀ ((hf.prodMap hg).nullMeasurableSet_preimage hs)]
  refine lintegral_congr fun x => ?_
  show map g μc (Prod.mk (f x) ⁻¹' s) = μc (Prod.mk x ⁻¹' (Prod.map f g ⁻¹' s))
  exact map_apply_of_aemeasurable hg (measurable_prodMk_left hs)
