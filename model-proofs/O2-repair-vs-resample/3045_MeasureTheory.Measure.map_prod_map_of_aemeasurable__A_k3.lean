/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.map_prod_map_of_aemeasurable
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/Prod.lean, line 842
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
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
  rw [map_congr hf.ae_eq_mk, map_congr hg.ae_eq_mk]
  have hfg : Prod.map f g =ᵐ[μa.prod μc] Prod.map (hf.mk f) (hg.mk g) := by
    have h1 := (quasiMeasurePreserving_fst (μ := μa) (ν := μc)).ae_eq_comp hf.ae_eq_mk
    have h2 := (quasiMeasurePreserving_snd (μ := μa) (ν := μc)).ae_eq_comp hg.ae_eq_mk
    filter_upwards [h1, h2] with p hp1 hp2
    exact Prod.ext hp1 hp2
  rw [map_congr hfg]
  have hf' := hf.measurable_mk
  have hg' := hg.measurable_mk
  ext s hs
  rw [prod_apply hs, map_apply (hf'.prodMap hg') hs, prod_apply (hf'.prodMap hg' hs),
    lintegral_map (measurable_measure_prodMk_left hs) hf']
  refine lintegral_congr fun x => ?_
  rw [map_apply hg' (measurable_prodMk_left hs)]
  rfl
