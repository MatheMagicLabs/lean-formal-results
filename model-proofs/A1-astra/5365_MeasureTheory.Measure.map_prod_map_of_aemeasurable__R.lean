/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.map_prod_map_of_aemeasurable
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/Prod.lean, line 842
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  have hf' : ∀ᵐ p ∂μa.prod μc, f p.1 = hf.mk f p.1 := by
    first
    | exact ae_prod_of_ae_fst hf.ae_eq_mk
    | exact ae_fst hf.ae_eq_mk
    | exact quasiMeasurePreserving_fst.ae hf.ae_eq_mk
  have hg' : ∀ᵐ p ∂μa.prod μc, g p.2 = hg.mk g p.2 := by
    first
    | exact ae_prod_of_ae_snd hg.ae_eq_mk
    | exact ae_snd hg.ae_eq_mk
    | exact quasiMeasurePreserving_snd.ae hg.ae_eq_mk
  have h :
      Prod.map f g =ᵐ[μa.prod μc] Prod.map (hf.mk f) (hg.mk g) := by
    filter_upwards [hf', hg'] with p hp hq
    exact Prod.ext hp hq
  rw [map_congr hf.ae_eq_mk, map_congr hg.ae_eq_mk, map_congr h]
  have hm : Measurable (Prod.map (hf.mk f) (hg.mk g)) := by
    fun_prop
  ext s hs
  rw [map_apply hm hs, prod_apply hs, prod_apply (hm hs)]
  first
  | rw [lintegral_map (measurable_measure_prodMk_left hs) hf.measurable_mk]
  | rw [lintegral_map hf.measurable_mk (measurable_measure_prodMk_left hs)]
  apply lintegral_congr
  intro a
  rw [map_apply hg.measurable_mk (measurable_prodMk_left hs)]
  rfl
