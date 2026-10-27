/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.limitProcess_ae_eq
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 191
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
  classical
  unfold limitProcess
  split_ifs with h
  · filter_upwards [h.choose_spec.2, hg] with ω hω hgω
    exact tendsto_nhds_unique hω hgω
  · exact (h ⟨g, mg, hg⟩).elim
