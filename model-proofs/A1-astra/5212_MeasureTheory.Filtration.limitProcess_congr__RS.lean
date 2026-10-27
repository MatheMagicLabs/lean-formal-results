/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.limitProcess_congr
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 199
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 2 (round 0 = first attempt)
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

@[gcongr]
lemma limitProcess_congr (hXY : X ≡ᵐ[P] Y) :
    𝓕.limitProcess X P =ᵐ[P] 𝓕.limitProcess Y P := by
  classical
  by_cases hι : Nonempty ι
  · letI : Nonempty ι := hι
    by_cases hX : HasLimitProcess X 𝓕 P
    · have hY : HasLimitProcess Y 𝓕 P := HasLimitProcess.congr hXY hX
      apply limitProcess_ae_eq stronglyMeasurable_limitProcess
      filter_upwards [hXY, hY.ae_tendsto_limitProcess] with ω hω hYω
      have hω' : (X · ω) = (Y · ω) := by
        simpa only [funext_iff] using hω
      rw [hω']
      exact hYω
    · have hY : ¬ HasLimitProcess Y 𝓕 P :=
        mt (hasLimitProcess_congr_iff hXY).mpr hX
      simp [limitProcess, hX, hY]
  · have h : X = Y := by
      funext i
      exact (hι ⟨i⟩).elim
    simp [h]
