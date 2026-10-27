/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.uniformOfFinset_apply
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Distributions/Uniform.lean, line 250
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
        simp [uniformOfFinset, Finset.sum_filter, Set.indicator_apply, Measure.dirac_apply']
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ = #{x ∈ s | x ∈ t} * (#s : ℝ≥0∞)⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = #{x ∈ s | x ∈ t} / #s := (div_eq_mul_inv _ _).symm
