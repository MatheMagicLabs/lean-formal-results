/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     aemeasurable_to_prop
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/AEMeasurable.lean, line 432
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  refine ⟨fun x => x ∈ toMeasurable μ (f ⁻¹' {True}), ?_, ?_⟩
  · apply measurable_to_prop
    simpa using measurableSet_toMeasurable μ (f ⁻¹' {True})
  · filter_upwards [h.toMeasurable_ae_eq] with x hx
    simpa using hx.symm
