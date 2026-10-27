/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.uniformOfFinset_apply_singleton
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Distributions/Uniform.lean, line 211
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 2 (round 0 = first attempt)
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

@[simp]
theorem uniformOfFinset_apply_singleton (a : α) :
    uniformOfFinset s {a} = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
  unfold uniformOfFinset
  split_ifs with h <;>
    simp [h, Measure.count_apply_finset, Set.indicator, Measure.restrict_apply,
      ProbabilityTheory.cond_apply, Set.inter_singleton_of_mem,
      Set.singleton_inter_of_mem, Set.inter_singleton_eq_empty,
      Set.singleton_inter_eq_empty, Measure.smul_apply, Measure.coe_finset_sum,
      Finset.sum_apply, Measure.dirac_apply', Finset.sum_ite_eq, Finset.sum_ite_eq',
      Measure.count_singleton, Finset.mem_coe, Finset.measurableSet,
      PMF.toMeasure_apply_singleton]
