/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.HasLimitProcess.comp
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 71
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
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

lemma HasLimitProcess.comp {f : E → F} (hX : HasLimitProcess X 𝓕 P) (hf : Continuous f) :
    HasLimitProcess (fun t ω ↦ f (X t ω)) 𝓕 P := by
  obtain ⟨X', hX'm, hX'⟩ := hX
  refine ⟨fun ω ↦ f (X' ω), ?_, ?_⟩
  · first
      | exact hf.comp_stronglyMeasurable hX'm
      | exact hX'm.continuous_comp hf
      | exact hf.measurable.comp hX'm
      | fun_prop
  · filter_upwards [hX'] with ω hω
    exact (hf.tendsto _).comp hω
