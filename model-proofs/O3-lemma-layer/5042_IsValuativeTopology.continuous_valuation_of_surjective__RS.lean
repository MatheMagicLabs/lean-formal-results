/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsValuativeTopology.continuous_valuation_of_surjective
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 142
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Valuation ValuativeRel IsValuativeTopology UniformSpace MonoidWithZeroHom ValueGroup₀
open Set Filter Topology
variable {R K Γ₀ : Type*}
section Ring
namespace IsValuativeTopology
variable [Ring R] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)
open WithZeroTopology
end IsValuativeTopology
end Ring
section DivisionRing
variable [DivisionRing K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
section InversionEstimate
end InversionEstimate
namespace IsValuativeTopology
variable [ValuativeRel K] [TopologicalSpace K] [IsValuativeTopology K]
section WithZeroTopology
variable [v.Compatible]
open WithZeroTopology

theorem continuous_valuation_of_surjective (hsurj : Function.Surjective v) : Continuous v := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : v x = 0
  · have hx0 : x = 0 := by
      first
        | exact (map_eq_zero v).mp hx
        | exact (Valuation.zero_iff v).mp hx
    subst hx0
    unfold ContinuousAt
    rw [map_zero, WithZeroTopology.tendsto_zero]
    intro γ hγ
    obtain ⟨a, rfl⟩ := hsurj γ
    have hset : {y : K | v y < v a} = {y : K | valuation K y < valuation K a} := by
      ext y
      simp only [Set.mem_setOf_eq, ← not_le]
      first
        | rw [← Valuation.Compatible.vle_iff_le (v := v) a y,
            ← Valuation.Compatible.vle_iff_le (v := valuation K) a y]
        | rw [← Valuation.Compatible.rel_iff_le (v := v) a y,
            ← Valuation.Compatible.rel_iff_le (v := valuation K) a y]
    have hmem : v 0 < v a := by
      rw [map_zero]
      exact lt_of_le_of_ne zero_le' (Ne.symm hγ)
    have hnhds : {y : K | v y < v a} ∈ 𝓝 (0 : K) := by
      first
        | exact (show IsOpen {y : K | v y < v a} by
            rw [hset]; exact isOpen_ball _).mem_nhds hmem
        | exact (show IsOpen {y : K | v y < v a} by
            rw [hset]; exact IsValuativeTopology.isOpen_ball _).mem_nhds hmem
        | (rw [hset, mem_nhds_zero_iff]
           have hne : valuation K a ≠ 0 := by
             intro h
             apply hγ
             have : a = 0 := (map_eq_zero (valuation K)).mp h
             rw [this, map_zero]
           exact ⟨Units.mk0 _ hne, fun y hy => hy⟩)
    exact hnhds
  · first
      | exact continuousAt_valuation_of_ne_zero v hx
      | exact continuousAt_valuation_of_ne_zero (v := v) hx
      | exact continuousAt_valuation_of_ne_zero hx
