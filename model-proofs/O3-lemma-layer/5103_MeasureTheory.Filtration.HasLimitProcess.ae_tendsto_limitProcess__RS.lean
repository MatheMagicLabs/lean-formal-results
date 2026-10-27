/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.HasLimitProcess.ae_tendsto_limitProcess
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 166
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
end HasLimitProcess
section limitProcess
section Def
variable [Zero E]
open scoped Classical in

lemma HasLimitProcess.ae_tendsto_limitProcess (h : HasLimitProcess X 𝓕 P) :
    ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (𝓕.limitProcess X P ω)) := by
  classical
  first
  | (rw [limitProcess, dif_pos h]
     first
     | exact (Classical.choose_spec h).2
     | exact (Classical.choose_spec h).1
     | exact Classical.choose_spec h)
  | (simp only [limitProcess, h, dite_true]
     first
     | exact (Classical.choose_spec h).2
     | exact (Classical.choose_spec h).1
     | exact Classical.choose_spec h)
