/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.map_prod_map_of_aemeasurable
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/Prod.lean, line 842
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
      ext s hs
      rw [prod_apply hs,
        map_apply (hf.measurable_mk.prodMap hg.measurable_mk) hs,
        prod_apply ((hf.measurable_mk.prodMap hg.measurable_mk) hs)]
      rw [lintegral_map (measurable_measure_prodMk_left hs) hf.measurable_mk]
      apply lintegral_congr
      intro x
      rw [map_apply hg.measurable_mk (measurable_prodMk_left hs)]
      rfl
    _ = map (Prod.map f g) (μa.prod μc) := by
      apply map_congr
      filter_upwards
        [quasiMeasurePreserving_fst.ae hf.ae_eq_mk,
         quasiMeasurePreserving_snd.ae hg.ae_eq_mk] with x hx hy
      exact Prod.ext hx.symm hy.symm
