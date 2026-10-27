/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.map_prod_map_of_aemeasurable
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/Prod.lean, line 842
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  have h1 : (fun p : α × γ => hf.mk f p.1) =ᵐ[μa.prod μc] fun p => f p.1 :=
    quasiMeasurePreserving_fst.ae_eq hf.ae_eq_mk.symm
  have h2 : (fun p : α × γ => hg.mk g p.2) =ᵐ[μa.prod μc] fun p => g p.2 :=
    quasiMeasurePreserving_snd.ae_eq hg.ae_eq_mk.symm
  have hfg : map (Prod.map f g) (μa.prod μc)
      = map (Prod.map (hf.mk f) (hg.mk g)) (μa.prod μc) := by
    apply map_congr
    filter_upwards [h1, h2] with p hp1 hp2
    exact Prod.ext hp1.symm hp2.symm
  have hm : Measurable (Prod.map (hf.mk f) (hg.mk g)) := by
    exact Measurable.prod (hf.measurable_mk.comp measurable_fst)
      (hg.measurable_mk.comp measurable_snd)
  rw [map_congr hf.ae_eq_mk, map_congr hg.ae_eq_mk, hfg]
  ext s hs
  rw [map_apply hm hs, prod_apply hs, prod_apply (hm hs),
    lintegral_map (measurable_measure_prodMk_left hs) hf.measurable_mk]
  apply lintegral_congr
  intro x
  rw [map_apply hg.measurable_mk (measurable_prodMk_left hs)]
  rfl
