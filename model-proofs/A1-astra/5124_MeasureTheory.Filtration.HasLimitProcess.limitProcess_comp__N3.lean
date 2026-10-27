/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.HasLimitProcess.limitProcess_comp
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 225
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
end Def
section Preserved
variable [IsDirectedOrder ι] [Nonempty ι]
section Basic
variable [T2Space E] [Zero E]
end Basic
section Maps
variable {F G : Type*} [Zero F] [TopologicalSpace F] [Zero G] [TopologicalSpace G]

@[to_fun limitProcess_fun_comp]
lemma HasLimitProcess.limitProcess_comp [Zero E] [T2Space F] {f : E → F} (hf : Continuous f)
    (hX : HasLimitProcess X 𝓕 P) :
    𝓕.limitProcess (fun t ω ↦ f (X t ω)) P =ᵐ[P] f ∘ (𝓕.limitProcess X P) := by
  have hY : HasLimitProcess (fun t ω ↦ f (X t ω)) 𝓕 P := by
    first
    | exact hX.comp hf
    | exact hX.comp_continuous hf
    | exact hX.continuous_comp hf
    | exact hf.comp_hasLimitProcess hX
  have hlimX :
      ∀ᵐ ω ∂P, Tendsto (fun t ↦ X t ω) atTop
        (𝓝 (𝓕.limitProcess X P ω)) := by
    first
    | exact hX.ae_tendsto_limitProcess
    | exact hX.tendsto_limitProcess
    | exact ae_tendsto_limitProcess hX
    | exact tendsto_limitProcess hX
  have hlimY :
      ∀ᵐ ω ∂P, Tendsto (fun t ↦ f (X t ω)) atTop
        (𝓝 (𝓕.limitProcess (fun t ω ↦ f (X t ω)) P ω)) := by
    first
    | exact hY.ae_tendsto_limitProcess
    | exact hY.tendsto_limitProcess
    | exact ae_tendsto_limitProcess hY
    | exact tendsto_limitProcess hY
  filter_upwards [hlimX, hlimY] with ω hω hω'
  exact tendsto_nhds_unique hω' ((hf.tendsto _).comp hω)
