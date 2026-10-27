/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.HasLimitProcess.limitProcess_comp₂
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 232
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
  refine limitProcess_ae_eq ?_ ?_
  · exact hf.comp_stronglyMeasurable
      ((stronglyMeasurable_limitProcess).prodMk stronglyMeasurable_limitProcess)
  · filter_upwards [hX.ae_tendsto_limitProcess, hY.ae_tendsto_limitProcess] with ω h1 h2
    exact (hf.tendsto _).comp (h1.prodMk_nhds h2)
