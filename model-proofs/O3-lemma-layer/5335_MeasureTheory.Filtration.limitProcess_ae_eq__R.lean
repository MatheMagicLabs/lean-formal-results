/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.limitProcess_ae_eq
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 191
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
end HasLimitProcess
section limitProcess
section Def
variable [Zero E]
open scoped Classical in
end Def
section Preserved
variable [IsDirectedOrder ι] [Nonempty ι]
section Basic
variable [T2Space E] [Zero E]

lemma limitProcess_ae_eq (mg : StronglyMeasurable[⨆ t, 𝓕 t] g)
    (hg : ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (g ω))) :
    𝓕.limitProcess X P =ᵐ[P] g := by
  unfold limitProcess
  split_ifs with h
  · have hs := Classical.choose_spec h
    first
    | (filter_upwards [hs.2, hg] with ω h1 h2
       exact tendsto_nhds_unique h1 h2)
    | (filter_upwards [hs.1, hg] with ω h1 h2
       exact tendsto_nhds_unique h1 h2)
  · exfalso
    apply h
    first
    | exact ⟨g, mg, hg⟩
    | (unfold HasLimitProcess; exact ⟨g, mg, hg⟩)
    | exact ⟨⟨g, mg, hg⟩⟩
