/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     aemeasurable_to_prop
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/AEMeasurable.lean, line 432
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  refine aemeasurable_to_countable' fun x => ?_
  by_cases hx : x
  · have : f ⁻¹' {x} = f ⁻¹' {True} := by
      ext a
      simp [hx]
    rw [this]
    exact h
  · have : f ⁻¹' {x} = (f ⁻¹' {True})ᶜ := by
      ext a
      simp [hx]
    rw [this]
    exact h.compl
