/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.limitProcess_congr
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 199
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 3 (round 0 = first attempt)
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
  have h : ∀ᵐ ω ∂P, ∀ i, X i ω = Y i ω := hXY
  by_cases hι : Nonempty ι
  swap
  · have hXY' : X = Y := funext fun i => (hι ⟨i⟩).elim
    subst hXY'
    exact EventuallyEq.rfl
  unfold limitProcess
  try unfold HasLimitProcess at *
  split_ifs with h1 h2 h2
  · have h1' := h1.choose_spec.2
    have h2' := h2.choose_spec.2
    have hne : (atTop : Filter ι).NeBot := by
      first
        | exact Filter.atTop_neBot_iff.mpr ⟨hι, inferInstance⟩
        | (haveI := hι; exact Filter.atTop_neBot)
        | (haveI := hι; infer_instance)
    filter_upwards [h1', h2', h] with ω h1ω h2ω hω
    have : (fun i => X i ω) = fun i => Y i ω := funext hω
    rw [this] at h1ω
    exact tendsto_nhds_unique' hne h1ω h2ω
  · exfalso
    apply h2
    refine ⟨h1.choose, h1.choose_spec.1, ?_⟩
    filter_upwards [h1.choose_spec.2, h] with ω h1ω hω
    have : (fun i => X i ω) = fun i => Y i ω := funext hω
    rw [this] at h1ω
    exact h1ω
  · exfalso
    apply h1
    refine ⟨h2.choose, h2.choose_spec.1, ?_⟩
    filter_upwards [h2.choose_spec.2, h] with ω h1ω hω
    have : (fun i => X i ω) = fun i => Y i ω := funext hω
    rw [this]
    exact h1ω
  · rfl
