/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.HasLimitProcess.limitProcess_comp₂
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 232
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

lemma HasLimitProcess.limitProcess_comp₂ [Zero E] [T2Space G] {f : E → F → G}
    (hf : Continuous f.uncurry) {Y : ι → Ω → F}
    (hX : HasLimitProcess X 𝓕 P) (hY : HasLimitProcess Y 𝓕 P) :
    𝓕.limitProcess (fun t ω ↦ f (X t ω) (Y t ω)) P =ᵐ[P]
      fun ω ↦ f (𝓕.limitProcess X P ω) (𝓕.limitProcess Y P ω) := by
  classical
  obtain ⟨hXm, hXt⟩ := Exists.choose_spec hX
  obtain ⟨hYm, hYt⟩ := Exists.choose_spec hY
  have hZ : HasLimitProcess (fun t ω ↦ f (X t ω) (Y t ω)) 𝓕 P := by
    unfold HasLimitProcess
    exact ⟨fun ω ↦ f (Exists.choose hX ω) (Exists.choose hY ω),
      hf.comp_stronglyMeasurable (hXm.prodMk hYm), by
        filter_upwards [hXt, hYt] with ω h1 h2
        exact (hf.tendsto _).comp (h1.prodMk_nhds h2)⟩
  obtain ⟨hZm, hZt⟩ := Exists.choose_spec hZ
  have eX : 𝓕.limitProcess X P = Exists.choose hX := by
    first
    | (rw [limitProcess, dif_pos hX])
    | (unfold limitProcess; exact dif_pos hX)
    | exact dif_pos hX
  have eY : 𝓕.limitProcess Y P = Exists.choose hY := by
    first
    | (rw [limitProcess, dif_pos hY])
    | (unfold limitProcess; exact dif_pos hY)
    | exact dif_pos hY
  have eZ : 𝓕.limitProcess (fun t ω ↦ f (X t ω) (Y t ω)) P = Exists.choose hZ := by
    first
    | (rw [limitProcess, dif_pos hZ])
    | (unfold limitProcess; exact dif_pos hZ)
    | exact dif_pos hZ
  filter_upwards [hXt, hYt, hZt] with ω h1 h2 h3
  rw [eX, eY, eZ]
  exact tendsto_nhds_unique h3 ((hf.tendsto _).comp (h1.prodMk_nhds h2))
