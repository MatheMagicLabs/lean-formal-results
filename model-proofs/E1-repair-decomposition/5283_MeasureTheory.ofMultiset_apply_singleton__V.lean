/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.ofMultiset_apply_singleton
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Distributions/Uniform.lean, line 306
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open scoped Finset MeasureTheory NNReal ENNReal
open TopologicalSpace MeasureTheory.Measure PMF ProbabilityTheory
noncomputable section
namespace MeasureTheory
variable {E : Type*} [MeasurableSpace E] {μ : Measure E}
namespace pdf
variable {Ω : Type*}
variable {_ : MeasurableSpace Ω} {P : Measure Ω}
namespace IsUniform
variable {X : Ω → ℝ} {s : Set ℝ}
end IsUniform
variable {X : Ω → E}
open scoped Classical in
end pdf
namespace Measure
variable {α : Type*} [MeasurableSpace α]
open scoped NNReal ENNReal
section UniformOfFinset
variable [MeasurableSingletonClass α] {s : Finset α} {a : α}
open scoped Classical in
section Measure
variable (t : Set α)
open scoped Classical in
end Measure
end UniformOfFinset
section UniformOfFintype
section Measure
end Measure
end UniformOfFintype
section OfMultiset
open scoped Classical in
variable [MeasurableSingletonClass α] {s : Multiset α}
open scoped Classical in

@[simp]
theorem ofMultiset_apply_singleton (a : α) : ofMultiset s {a} = s.count a / (Multiset.card s) := by
  classical
  simp [ofMultiset, div_eq_mul_inv, mul_comm]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    simp [Pi.single_apply, hba, Ne.symm hba]
  · intro ha
    have hc : s.count a = 0 :=
      Multiset.count_eq_zero.mpr (by simpa using ha)
    simp [hc]
