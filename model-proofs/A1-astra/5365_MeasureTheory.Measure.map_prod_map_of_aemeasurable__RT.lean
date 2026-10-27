/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.map_prod_map_of_aemeasurable
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/Prod.lean, line 842
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 0 (round 0 = first attempt)
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
  ext s hs
  rw [prod_apply hs, map_apply_of_aemeasurable (hf.prodMap hg) hs,
    prod_apply₀ ((hf.prodMap hg).nullMeasurableSet_preimage hs),
    lintegral_map' (measurable_measure_prodMk_left hs).aemeasurable hf]
  apply lintegral_congr
  intro x
  exact map_apply_of_aemeasurable hg (measurable_prodMk_left hs)
