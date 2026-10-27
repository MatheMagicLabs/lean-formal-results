/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.HasLimitProcess.ae_tendsto_limitProcess
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 166
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm N3, verified in round 0 (round 0 = first attempt)
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
end HasLimitProcess
section limitProcess
section Def
variable [Zero E]
open scoped Classical in

lemma HasLimitProcess.ae_tendsto_limitProcess (h : HasLimitProcess X 𝓕 P) :
    ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (𝓕.limitProcess X P ω)) := by
  classical
  simpa only [limitProcess, dif_pos h] using h.choose_spec.2
