/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.HasLimitProcess.limitProcess_comp₂
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 232
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 1 (round 0 = first attempt)
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

lemma HasLimitProcess.limitProcess_comp₂ [Zero E] [T2Space G] {f : E → F → G}
    (hf : Continuous f.uncurry) {Y : ι → Ω → F}
    (hX : HasLimitProcess X 𝓕 P) (hY : HasLimitProcess Y 𝓕 P) :
    𝓕.limitProcess (fun t ω ↦ f (X t ω) (Y t ω)) P =ᵐ[P]
      fun ω ↦ f (𝓕.limitProcess X P ω) (𝓕.limitProcess Y P ω) := by
  filter_upwards [hX.ae_tendsto_limitProcess, hY.ae_tendsto_limitProcess,
    (hX.comp₂ hY hf).ae_tendsto_limitProcess] with ω hXω hYω hXYω
  exact tendsto_nhds_unique hXYω
    (hf.continuousAt.tendsto.comp (hXω.prodMk_nhds hYω))
