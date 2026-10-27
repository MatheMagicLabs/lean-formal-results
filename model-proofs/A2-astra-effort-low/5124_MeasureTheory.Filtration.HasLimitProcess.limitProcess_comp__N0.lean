/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.HasLimitProcess.limitProcess_comp
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 225
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm N0, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
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
  have hcomp : HasLimitProcess (fun t ω ↦ f (X t ω)) 𝓕 P := by
    first
    | exact hX.comp hf
    | exact hX.comp hf.measurable
    | exact hX.continuous_comp hf
    | exact hf.comp_hasLimitProcess hX
    | exact hX.mono fun ω hω ↦ by
        obtain ⟨x, hx⟩ := hω
        exact ⟨f x, (hf.tendsto x).comp hx⟩
  have h₁ : ∀ᵐ ω ∂P,
      Tendsto (fun t ↦ X t ω) atTop (𝓝 (𝓕.limitProcess X P ω)) := by
    first
    | exact hX.tendsto_limitProcess
    | exact hX.ae_tendsto_limitProcess
    | exact hX.tendsto
  have h₂ : ∀ᵐ ω ∂P,
      Tendsto (fun t ↦ f (X t ω)) atTop
        (𝓝 (𝓕.limitProcess (fun t ω ↦ f (X t ω)) P ω)) := by
    first
    | exact hcomp.tendsto_limitProcess
    | exact hcomp.ae_tendsto_limitProcess
    | exact hcomp.tendsto
  filter_upwards [h₁, h₂] with ω hω hω'
  exact tendsto_nhds_unique hω' ((hf.tendsto _).comp hω)
