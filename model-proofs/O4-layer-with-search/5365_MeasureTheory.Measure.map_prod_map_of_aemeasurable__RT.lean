/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.map_prod_map_of_aemeasurable
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/Prod.lean, line 842
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
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
  have h1 : (fun p : α × γ => f p.1) =ᵐ[μa.prod μc] fun p => hf.mk f p.1 :=
    (quasiMeasurePreserving_fst).ae_eq hf.ae_eq_mk
  have h2 : (fun p : α × γ => g p.2) =ᵐ[μa.prod μc] fun p => hg.mk g p.2 :=
    (quasiMeasurePreserving_snd).ae_eq hg.ae_eq_mk
  have h3 : Prod.map f g =ᵐ[μa.prod μc] Prod.map (hf.mk f) (hg.mk g) := by
    filter_upwards [h1, h2] with p hp1 hp2
    simp only [Prod.map]
    rw [hp1, hp2]
  rw [map_congr hf.ae_eq_mk, map_congr hg.ae_eq_mk, map_congr h3]
  have hF := hf.measurable_mk
  have hG := hg.measurable_mk
  ext s hs
  rw [map_apply (hF.prodMap hG) hs, prod_apply hs,
    prod_apply ((hF.prodMap hG) hs),
    lintegral_map (measurable_measure_prodMk_left hs) hF]
  refine lintegral_congr fun x => ?_
  rw [map_apply hG (measurable_prodMk_left hs)]
  rfl
