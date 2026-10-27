/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.uniformOfFinset_apply
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Distributions/Uniform.lean, line 250
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

theorem uniformOfFinset_apply :
    uniformOfFinset s t = #{x ∈ s | x ∈ t} / #s :=
  calc
    uniformOfFinset s t = ∑ x ∈ s with x ∈ t, (#s : ℝ≥0∞)⁻¹ := by
        classical
        simp [uniformOfFinset, Finset.sum_filter, Finset.mul_sum,
          Finset.sum_mul, Measure.dirac_apply', mul_comm]
        simp only [Set.indicator_apply, Pi.one_apply, mul_ite, mul_one, mul_zero]
        rw [← Finset.sum_filter]
        simp [mul_comm]
      _ = #{x ∈ s | x ∈ t} / #s := by
        simp [div_eq_mul_inv, mul_comm]
