/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.limitProcess_ae_eq
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 191
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  LS1-leanstral-loop, arm L3, verified in round 0 (round 0 = first attempt)
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 in a fixed check-and-repair loop: L1 = 1 candidate per round, L3 = up to 3
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

lemma limitProcess_ae_eq (mg : StronglyMeasurable[⨆ t, 𝓕 t] g)
    (hg : ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (g ω))) :
    𝓕.limitProcess X P =ᵐ[P] g := by
  have hX : HasLimitProcess X 𝓕 P := ⟨g, mg, hg⟩
  have hlim := hX.ae_tendsto_limitProcess
  filter_upwards [hg, hlim] with ω hgω hlimω
  exact tendsto_nhds_unique hlimω hgω
