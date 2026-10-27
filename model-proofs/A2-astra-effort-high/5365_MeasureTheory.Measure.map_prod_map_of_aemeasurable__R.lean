/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.map_prod_map_of_aemeasurable
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/Prod.lean, line 842
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

noncomputable section
open ENNReal MeasureTheory Set Function Real ENNReal MeasurableSpace MeasureTheory.Measure
open TopologicalSpace hiding generateFrom
open Filter hiding prod_eq map
variable {α β γ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable {μ μ' : Measure α} {ν ν' : Measure β} {τ : Measure γ}
namespace MeasureTheory
namespace Measure
variable [SFinite ν]
open IsUnifLocDoublingMeasure in
variable [SFinite μ]

theorem map_prod_map_of_aemeasurable {δ} [MeasurableSpace δ] {f : α → β} {g : γ → δ}
    (μa : Measure α) (μc : Measure γ) [SFinite μc] (hf : AEMeasurable f μa)
    (hg : AEMeasurable g μc) :
    (map f μa).prod (map g μc) = map (Prod.map f g) (μa.prod μc) := by
  calc
    (map f μa).prod (map g μc) =
        (map (hf.mk f) μa).prod (map (hg.mk g) μc) := by
      rw [map_congr hf.ae_eq_mk, map_congr hg.ae_eq_mk]
    _ = map (Prod.map (hf.mk f) (hg.mk g)) (μa.prod μc) := by
      have hfg : Measurable (Prod.map (hf.mk f) (hg.mk g)) :=
        (hf.measurable_mk.comp measurable_fst).prodMk
          (hg.measurable_mk.comp measurable_snd)
      ext s hs
      rw [prod_apply hs, map_apply hfg hs, prod_apply (hfg hs)]
      rw [lintegral_map (measurable_measure_prodMk_left hs) hf.measurable_mk]
      apply lintegral_congr
      intro a
      have hsection : MeasurableSet (Prod.mk (hf.mk f a) ⁻¹' s) :=
        (measurable_const.prodMk measurable_id) hs
      rw [map_apply hg.measurable_mk hsection]
      rfl
    _ = map (Prod.map f g) (μa.prod μc) := by
      apply map_congr
      filter_upwards
        [quasiMeasurePreserving_fst.ae hf.ae_eq_mk,
         quasiMeasurePreserving_snd.ae hg.ae_eq_mk] with p hp hq
      exact Prod.ext hp.symm hq.symm
