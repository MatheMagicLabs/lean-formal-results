/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.HasLimitProcess.comp
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 71
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm N1, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  rcases hX with ⟨g, hg, hlim⟩
  refine ⟨f ∘ g, hf.comp_stronglyMeasurable hg, ?_⟩
  filter_upwards [hlim] with ω hω
  exact (hf.tendsto (g ω)).comp hω
