/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.uniformOfFinset_apply_singleton
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Distributions/Uniform.lean, line 211
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
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
  classical
  by_cases h : a ∈ s
  · simp only [h, if_true]
    first
    | simp [uniformOfFinset, ProbabilityTheory.uniformOn_apply s.finite_toSet,
        Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr (Finset.mem_coe.mpr h)),
        Measure.count_apply_finset, ENNReal.div_eq_inv_mul]
    | simp [uniformOfFinset, Measure.dirac_apply', Set.indicator, Finset.sum_ite_eq', h]
    | simp [uniformOfFinset, h]
  · simp only [h, if_false]
    first
    | simp [uniformOfFinset, ProbabilityTheory.uniformOn_apply s.finite_toSet,
        Set.inter_singleton_eq_empty.mpr (fun h' => h (Finset.mem_coe.mp h'))]
    | simp [uniformOfFinset, Measure.dirac_apply', Set.indicator, Finset.sum_ite_eq', h]
    | simp [uniformOfFinset, h]
