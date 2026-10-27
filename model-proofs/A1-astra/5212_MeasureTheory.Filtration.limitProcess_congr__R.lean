/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.limitProcess_congr
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 199
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 2 (round 0 = first attempt)
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
  cases isEmpty_or_nonempty ι with
  | inl h =>
    letI := h
    have hEq : X = Y := funext fun i => isEmptyElim i
    subst Y
    exact Filter.EventuallyEq.rfl
  | inr h =>
    letI := h
    have hfun : ∀ᵐ ω ∂P, (fun i => X i ω) = (fun i => Y i ω) := by
      filter_upwards [hXY] with ω hω
      first
      | exact hω
      | exact funext hω
    have hlim : ∀ f : Ω → E,
        (∀ᵐ ω ∂P, Tendsto (fun i => X i ω) atTop (𝓝 (f ω))) ↔
        (∀ᵐ ω ∂P, Tendsto (fun i => Y i ω) atTop (𝓝 (f ω))) := by
      intro f
      apply Filter.eventually_congr
      filter_upwards [hfun] with ω hω
      rw [hω]
    have hHas : 𝓕.HasLimitProcess X P ↔ 𝓕.HasLimitProcess Y P := by
      simp only [HasLimitProcess, hlim]
    by_cases hX : 𝓕.HasLimitProcess X P
    · have hY := hHas.mp hX
      have hc : hX.choose =ᵐ[P] hY.choose := by
        filter_upwards [hX.choose_spec.2, hY.choose_spec.2, hfun] with ω hx hy hω
        rw [hω] at hx
        exact tendsto_nhds_unique hx hy
      simpa only [limitProcess, dif_pos hX, dif_pos hY] using hc
    · have hY : ¬𝓕.HasLimitProcess Y P := fun hY => hX (hHas.mpr hY)
      simp only [limitProcess, dif_neg hX, dif_neg hY]
      exact Filter.EventuallyEq.rfl
