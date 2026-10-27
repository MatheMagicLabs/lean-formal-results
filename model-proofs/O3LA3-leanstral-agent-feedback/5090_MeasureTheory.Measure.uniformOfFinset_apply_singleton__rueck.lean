/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.uniformOfFinset_apply_singleton
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Distributions/Uniform.lean, line 211
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA3-leanstral-agent-feedback, arm rueck, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent with goal-state feedback (arm rueck)
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

@[simp]
theorem uniformOfFinset_apply_singleton (a : α) :
    uniformOfFinset s {a} = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
  classical
  simp [uniformOfFinset, dirac_apply, Pi.single_apply, smul_eq_mul, Finset.sum_ite_eq]
