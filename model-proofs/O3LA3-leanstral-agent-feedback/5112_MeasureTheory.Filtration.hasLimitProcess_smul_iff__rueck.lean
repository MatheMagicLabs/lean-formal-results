/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.hasLimitProcess_smul_iff
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 91
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA3-leanstral-agent-feedback, arm rueck, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent with goal-state feedback (arm rueck)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open MeasureTheory Filter
open scoped Topology ENNReal NNReal
namespace MeasureTheory.Filtration
variable {ι Ω E F G : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} [TopologicalSpace E]
section HasLimitProcess

@[to_additive]
lemma hasLimitProcess_smul_iff {G : Type*} [Group G] [MulAction G E] [ContinuousConstSMul G E]
    {c : G} :
    HasLimitProcess (c • X) 𝓕 P ↔ HasLimitProcess X 𝓕 P where
  mp h := by
    simpa [smul_smul, inv_mul_cancel, one_smul] using h.smul (c⁻¹)
  mpr h := h.smul c
