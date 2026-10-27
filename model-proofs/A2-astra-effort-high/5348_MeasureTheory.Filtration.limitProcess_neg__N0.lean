/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.limitProcess_neg
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 263
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm N0, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
variable [T2Space E] [T2Space F]

@[to_fun limitProcess_fun_neg]
lemma limitProcess_neg [AddGroup E] [ContinuousNeg E] (X : ι → Ω → E) :
    𝓕.limitProcess (-X) P =ᵐ[P] -𝓕.limitProcess X P := by
  classical
  have hneg (Y : ι → Ω → E) (hY : 𝓕.HasLimitProcess Y P) :
      𝓕.HasLimitProcess (-Y) P := by
    rcases hY with ⟨f, hf, hY⟩
    refine ⟨-f, hf.neg, ?_⟩
    filter_upwards [hY] with ω hω
    exact hω.neg
  unfold limitProcess
  split_ifs with h₁ h₂ h₂
  · filter_upwards [h₁.choose_spec.2, h₂.choose_spec.2] with ω h₁ω h₂ω
    exact tendsto_nhds_unique h₁ω h₂ω.neg
  · exact (h₂ (by simpa only [neg_neg] using hneg (-X) h₁)).elim
  · exact (h₁ (hneg X h₂)).elim
  · simp
