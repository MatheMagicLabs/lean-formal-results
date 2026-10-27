/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.uniformOfFinset_apply_singleton
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Distributions/Uniform.lean, line 211
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA-leanstral-agent, arm -, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 as a tool-using agent (Mistral Vibe)
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
  rw [uniformOfFinset, finsetSum_apply]
  simp_rw [smul_apply]
  by_cases h : a ∈ s
  · rw [if_pos h]
    have hsing : MeasurableSet ({a} : Set α) := MeasurableSet.singleton a
    simp_rw [dirac_apply' _ hsing, Set.indicator_apply]
    -- ∑ x ∈ s, (s.card⁻¹ : ℝ≥0∞) • (if x ∈ {a} then 1 else 0) = (s.card : ℝ≥0∞)⁻¹
    have hsum : (∑ x ∈ s, (if x ∈ ({a} : Set α) then (1 : ℝ≥0∞) else 0)) =
        (if a ∈ s then (1 : ℝ≥0∞) else 0) := by
      simp
    calc
      (∑ x ∈ s, ((s.card : ℝ≥0∞)⁻¹) • (if x ∈ ({a} : Set α) then (1 : ℝ≥0∞) else 0))
          = ((s.card : ℝ≥0∞)⁻¹) • (∑ x ∈ s, (if x ∈ ({a} : Set α) then (1 : ℝ≥0∞) else 0)) := by
        simp [Finset.smul_sum]
      _ = ((s.card : ℝ≥0∞)⁻¹) • (if a ∈ s then (1 : ℝ≥0∞) else 0) := by rw [hsum]
      _ = ((s.card : ℝ≥0∞)⁻¹) • (1 : ℝ≥0∞) := by simp [h]
      _ = (s.card : ℝ≥0∞)⁻¹ := by simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hx_not_mem : x ∉ ({a} : Set α) := by
      intro hmem; apply h; simpa [Set.mem_singleton_iff.mp hmem] using hx
    have hsing : MeasurableSet ({a} : Set α) := MeasurableSet.singleton a
    rw [dirac_apply' x hsing, Set.indicator_apply, if_neg hx_not_mem, smul_zero]
