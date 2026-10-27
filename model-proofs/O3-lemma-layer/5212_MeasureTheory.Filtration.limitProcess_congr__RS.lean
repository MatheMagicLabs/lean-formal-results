/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.limitProcess_congr
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 199
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
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

@[gcongr]
lemma limitProcess_congr (hXY : X ≡ᵐ[P] Y) :
    𝓕.limitProcess X P =ᵐ[P] 𝓕.limitProcess Y P := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hxy : X = Y := funext fun i => isEmptyElim i
    subst hxy
    exact Filter.EventuallyEq.rfl
  · by_cases h : HasLimitProcess X 𝓕 P
    · have hXY' : ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := hXY
      refine (limitProcess_ae_eq stronglyMeasurable_limitProcess ?_).symm
      filter_upwards [h.ae_tendsto_limitProcess, hXY'] with ω h1 h2
      have e : (fun t => Y t ω) = fun t => X t ω := funext fun t => (h2 t).symm
      rw [e]
      exact h1
    · have h' : ¬ HasLimitProcess Y 𝓕 P := by
        rwa [← hasLimitProcess_congr_iff hXY]
      have e1 : 𝓕.limitProcess X P = 𝓕.limitProcess Y P := by
        simp [limitProcess, h, h']
      exact Filter.Eventually.of_forall fun ω => congrFun e1 ω
