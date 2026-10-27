/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.HasLimitProcess.comp
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 71
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  rcases hX with ⟨Y, hY, hlim⟩
  refine ⟨f ∘ Y, hf.comp_stronglyMeasurable hY, ?_⟩
  exact hlim.mono fun ω hω ↦ (hf.tendsto (Y ω)).comp hω
