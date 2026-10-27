/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.HasLimitProcess.limitProcess_comp
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 225
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm N0, verified in round 0 (round 0 = first attempt)
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
  filter_upwards [hX.ae_tendsto_limitProcess,
    (hX.comp hf).ae_tendsto_limitProcess] with ω hω hfω
  exact tendsto_nhds_unique hfω (hf.continuousAt.tendsto.comp hω)
