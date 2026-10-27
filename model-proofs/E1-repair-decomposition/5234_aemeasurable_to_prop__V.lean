/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     aemeasurable_to_prop
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/AEMeasurable.lean, line 432
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
  let t := toMeasurable μ (f ⁻¹' {True})
  have ht : MeasurableSet t := measurableSet_toMeasurable μ _
  refine ⟨fun x => x ∈ t, ?_, ?_⟩
  · intro s hs
    by_cases htrue : True ∈ s <;> by_cases hfalse : False ∈ s
    · convert (MeasurableSet.univ : MeasurableSet (univ : Set α)) using 1
      ext x
      by_cases hx : x ∈ t <;> simp [hx, htrue, hfalse]
    · convert ht using 1
      ext x
      by_cases hx : x ∈ t <;> simp [hx, htrue, hfalse]
    · convert ht.compl using 1
      ext x
      by_cases hx : x ∈ t <;> simp [hx, htrue, hfalse]
    · convert (MeasurableSet.empty : MeasurableSet (∅ : Set α)) using 1
      ext x
      by_cases hx : x ∈ t <;> simp [hx, htrue, hfalse]
  · filter_upwards [h.toMeasurable_ae_eq] with x hx
    simpa [t] using hx.symm
