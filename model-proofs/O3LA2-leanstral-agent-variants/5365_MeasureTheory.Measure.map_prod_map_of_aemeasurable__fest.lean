/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.map_prod_map_of_aemeasurable
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/Prod.lean, line 842
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA2-leanstral-agent-variants, arm fest, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent on the 29 theorems O3LA left open: neu = fresh restart, fest = fixed instruction, staffel = staged budget
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
  have hfg : AEMeasurable (Prod.map f g) (μa.prod μc) := hf.prodMap hg
  ext s hs
  have h_preimage_null_measurable : NullMeasurableSet ((Prod.map f g) ⁻¹' s) (μa.prod μc) :=
    hfg.nullMeasurable hs
  rw [prod_apply hs, map_apply_of_aemeasurable hfg hs, prod_apply₀ h_preimage_null_measurable]
  have h_meas : AEMeasurable (fun x => (map g μc) (Prod.mk x ⁻¹' s)) (map f μa) := by
    have h_eq : (fun x => (map g μc) (Prod.mk x ⁻¹' s)) =
      (fun x => (μc.map g) (Prod.mk x ⁻¹' s)) := by
      ext x; simp [map_apply_of_aemeasurable hg (measurable_prodMk_left hs)]
    rw [h_eq]
    exact (measurable_measure_prodMk_left hs).aemeasurable
  rw [lintegral_map' h_meas hf]
  simp_rw [map_apply_of_aemeasurable hg (measurable_prodMk_left hs)]
  have h_set (a : α) : g ⁻¹' (Prod.mk (f a) ⁻¹' s) = Prod.mk a ⁻¹' ((Prod.map f g) ⁻¹' s) := by
    ext c; simp [Prod.map, Prod.mk]
  refine lintegral_congr (fun a => ?_)
  rw [h_set a]
