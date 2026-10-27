/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.HasLimitProcess.limitProcess_comp
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 225
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
end Basic
section Maps
variable {F G : Type*} [Zero F] [TopologicalSpace F] [Zero G] [TopologicalSpace G]

@[to_fun limitProcess_fun_comp]
lemma HasLimitProcess.limitProcess_comp [Zero E] [T2Space F] {f : E → F} (hf : Continuous f)
    (hX : HasLimitProcess X 𝓕 P) :
    𝓕.limitProcess (fun t ω ↦ f (X t ω)) P =ᵐ[P] f ∘ (𝓕.limitProcess X P) := by
  have h1 : ∀ᵐ ω ∂P, Tendsto (fun t ↦ X t ω) atTop (𝓝 (𝓕.limitProcess X P ω)) := by
    unfold limitProcess
    rw [dif_pos hX]
    exact hX.choose_spec.2
  have hfX : HasLimitProcess (fun t ω ↦ f (X t ω)) 𝓕 P := by
    obtain ⟨Y, hYm, hY⟩ := hX
    exact ⟨fun ω ↦ f (Y ω), hf.comp_stronglyMeasurable hYm,
      hY.mono fun ω h ↦ (hf.tendsto _).comp h⟩
  have h2 : ∀ᵐ ω ∂P, Tendsto (fun t ↦ f (X t ω)) atTop
      (𝓝 (𝓕.limitProcess (fun t ω ↦ f (X t ω)) P ω)) := by
    unfold limitProcess
    rw [dif_pos hfX]
    exact hfX.choose_spec.2
  filter_upwards [h1, h2] with ω h1 h2
  exact tendsto_nhds_unique h2 ((hf.tendsto _).comp h1)
