/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.hasLimitProcess_smul_iff
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 91
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 3 (round 0 = first attempt)
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

@[to_additive]
lemma hasLimitProcess_smul_iff {G : Type*} [Group G] [MulAction G E] [ContinuousConstSMul G E]
    {c : G} :
    HasLimitProcess (c • X) 𝓕 P ↔ HasLimitProcess X 𝓕 P where
  mp h := by
    { obtain ⟨Y, hY, hlim⟩ := h; exact ⟨c⁻¹ • Y, hY.const_smul c⁻¹, by filter_upwards [hlim] with ω hω; simpa [smul_smul] using hω.const_smul c⁻¹⟩ }; mpr h := by { obtain ⟨Y, hY, hlim⟩ := h; exact ⟨c • Y, hY.const_smul c, by filter_upwards [hlim] with ω hω; simpa using hω.const_smul c⟩ }
