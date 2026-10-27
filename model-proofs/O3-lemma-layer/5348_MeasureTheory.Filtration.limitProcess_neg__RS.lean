/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.limitProcess_neg
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 263
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
variable [T2Space E] [T2Space F]

@[to_fun limitProcess_fun_neg]
lemma limitProcess_neg [AddGroup E] [ContinuousNeg E] (X : ι → Ω → E) :
    𝓕.limitProcess (-X) P =ᵐ[P] -𝓕.limitProcess X P := by
  by_cases h : HasLimitProcess X 𝓕 P
  · exact h.limitProcess_comp continuous_neg
  · have h' : ¬ HasLimitProcess (-X) 𝓕 P := by
      intro h'
      apply h
      have := h'.comp continuous_neg
      simpa using this
    unfold limitProcess
    simp only [dif_neg h, dif_neg h']
    first
      | rfl
      | (filter_upwards with ω; simp)
      | simp
