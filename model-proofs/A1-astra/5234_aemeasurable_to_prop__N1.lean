/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     aemeasurable_to_prop
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/AEMeasurable.lean, line 432
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm N1, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open MeasureTheory MeasureTheory.Measure Filter Set Function ENNReal
variable {ι α β γ δ R : Type*} {m0 : MeasurableSpace α} [MeasurableSpace β] [MeasurableSpace γ]
section
namespace AEMeasurable
end AEMeasurable
open scoped Interval in
end
section Zero
variable [Zero β]
end Zero
section prop

theorem aemeasurable_to_prop {f : α → Prop} (h : NullMeasurableSet (f ⁻¹' {True}) μ) :
    AEMeasurable f μ := by
  classical
  let s := toMeasurable μ (f ⁻¹' {True})
  have hs : MeasurableSet s := measurableSet_toMeasurable μ _
  have hg : Measurable (fun x => x ∈ s) := by
    intro t ht
    by_cases hT : True ∈ t
    · by_cases hF : False ∈ t
      · have heq : (fun x => x ∈ s) ⁻¹' t = univ := by
          ext x
          by_cases hx : x ∈ s <;> simp [hx, hT, hF]
        rw [heq]
        exact MeasurableSet.univ
      · have heq : (fun x => x ∈ s) ⁻¹' t = s := by
          ext x
          by_cases hx : x ∈ s <;> simp [hx, hT, hF]
        rw [heq]
        exact hs
    · by_cases hF : False ∈ t
      · have heq : (fun x => x ∈ s) ⁻¹' t = sᶜ := by
          ext x
          by_cases hx : x ∈ s <;> simp [hx, hT, hF]
        rw [heq]
        exact hs.compl
      · have heq : (fun x => x ∈ s) ⁻¹' t = ∅ := by
          ext x
          by_cases hx : x ∈ s <;> simp [hx, hT, hF]
        rw [heq]
        exact MeasurableSet.empty
  apply hg.aemeasurable.congr
  filter_upwards [h.toMeasurable_ae_eq] with x hx
  simpa [s] using hx
