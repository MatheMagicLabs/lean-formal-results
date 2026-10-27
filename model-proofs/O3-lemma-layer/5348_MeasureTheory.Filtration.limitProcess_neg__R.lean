/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.limitProcess_neg
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 263
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
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
  classical
  by_cases h : 𝓕.HasLimitProcess X P
  · have h' : 𝓕.HasLimitProcess (-X) P := by
      obtain ⟨g, hg, hgt⟩ := id h
      exact ⟨-g, hg.neg, hgt.mono fun ω hω => by simpa [Pi.neg_apply] using hω.neg⟩
    simp only [limitProcess, dif_pos h, dif_pos h']
    filter_upwards [h.choose_spec.2, h'.choose_spec.2] with ω h1 h2
    simp only [Pi.neg_apply] at h2 ⊢
    exact tendsto_nhds_unique h2 h1.neg
  · have h' : ¬ 𝓕.HasLimitProcess (-X) P := by
      rintro ⟨g, hg, hgt⟩
      exact h ⟨-g, hg.neg, hgt.mono fun ω hω => by simpa [Pi.neg_apply] using hω.neg⟩
    simp only [limitProcess, dif_neg h, dif_neg h']
    filter_upwards with ω
    simp
