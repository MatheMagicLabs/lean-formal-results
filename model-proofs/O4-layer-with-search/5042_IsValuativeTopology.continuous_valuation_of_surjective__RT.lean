/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsValuativeTopology.continuous_valuation_of_surjective
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 142
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
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
  rcases eq_or_ne (v x) 0 with h | h
  · rw [ContinuousAt, h, WithZeroTopology.tendsto_zero]
    intro γ hγ
    obtain ⟨y, rfl⟩ := hsurj γ
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hγ (map_zero v)
    have key : ∀ a b : K, valuation K a < valuation K b ↔ v a < v b := by
      intro a b
      rw [← not_le, ← not_le, ← Valuation.vle_iff_le (v := valuation K),
        ← Valuation.vle_iff_le (v := v)]
    rw [Filter.Eventually, IsValuativeTopology.mem_nhds_iff']
    refine ⟨Units.mk0 (valuation K y) ((Valuation.ne_zero_iff _).2 hy0), ?_⟩
    intro z hz
    simp only [Set.mem_setOf_eq, Units.val_mk0] at hz ⊢
    rw [key] at hz
    calc v z = v ((z - x) + x) := by rw [sub_add_cancel]
      _ ≤ max (v (z - x)) (v x) := v.map_add _ _
      _ = v (z - x) := by rw [h]; exact max_eq_left zero_le'
      _ < v y := hz
  · exact continuousAt_valuation_of_ne_zero v h
