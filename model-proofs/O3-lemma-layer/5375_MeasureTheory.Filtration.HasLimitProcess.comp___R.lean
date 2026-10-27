/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.HasLimitProcess.comp₂
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 77
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open MeasureTheory Filter
open scoped Topology ENNReal NNReal
namespace MeasureTheory.Filtration
variable {ι Ω E F G : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} [TopologicalSpace E]
section HasLimitProcess

lemma HasLimitProcess.comp₂ {f : E → F → G} (hX : HasLimitProcess X 𝓕 P)
    (hZ : HasLimitProcess Z 𝓕 P) (hf : Continuous f.uncurry) :
    HasLimitProcess (fun t ω ↦ f (X t ω) (Z t ω)) 𝓕 P := by
  obtain ⟨Y, hYm, hY⟩ := hX
  obtain ⟨W, hWm, hW⟩ := hZ
  refine ⟨fun ω ↦ f (Y ω) (W ω), ?_, ?_⟩
  · first
      | exact hf.comp_stronglyMeasurable (hYm.prodMk hWm)
      | exact hf.comp_aestronglyMeasurable (hYm.prodMk hWm)
      | exact hf.measurable.comp (hYm.prodMk hWm)
      | exact hf.aemeasurable.comp_aemeasurable (hYm.prodMk hWm)
  · filter_upwards [hY, hW] with ω h1 h2
    exact (hf.tendsto (Y ω, W ω)).comp (h1.prodMk_nhds h2)
