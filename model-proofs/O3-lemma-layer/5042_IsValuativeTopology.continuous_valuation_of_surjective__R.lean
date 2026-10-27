/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsValuativeTopology.continuous_valuation_of_surjective
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 142
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
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
  have hball : ∀ a : K, a ≠ 0 → {y : K | v y < v a} ∈ 𝓝 (0 : K) := by
    intro a ha
    have key : ∀ y, valuation K y < valuation K a ↔ v y < v a := by
      intro y
      rw [← not_le, ← not_le]
      apply not_congr
      first
        | exact ((Valuation.Compatible.rel_iff_le (v := valuation K) a y).symm.trans
            (Valuation.Compatible.rel_iff_le (v := v) a y))
        | exact ((Valuation.Compatible.vle_iff_le (v := valuation K) a y).symm.trans
            (Valuation.Compatible.vle_iff_le (v := v) a y))
    have h0 : valuation K a ≠ 0 := by simpa using ha
    have : {y : K | valuation K y < valuation K a} ∈ 𝓝 (0 : K) := by
      first
        | exact (mem_nhds_zero_iff _).2 ⟨Units.mk0 _ h0, fun y hy => hy⟩
        | exact (isOpen_ball _).mem_nhds (by simp [zero_lt_iff, ha])
        | exact (isOpen_ball _).mem_nhds (by simpa [zero_lt_iff] using h0)
    convert this using 1
    ext y
    exact (key y).symm
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    unfold ContinuousAt
    rw [map_zero, WithZeroTopology.tendsto_zero]
    intro γ hγ
    obtain ⟨a, rfl⟩ := hsurj γ
    have ha : a ≠ 0 := by
      rintro rfl
      exact hγ (map_zero v)
    exact hball a ha
  · unfold ContinuousAt
    have hvx : v x ≠ 0 := by simpa using hx
    rw [WithZeroTopology.tendsto_of_ne_zero hvx]
    have h1 : {y : K | v (y - x) < v x} ∈ 𝓝 x := by
      have hc : Tendsto (fun y : K => y - x) (𝓝 x) (𝓝 0) := by
        have hcont : Continuous fun y : K => y - x := continuous_id.sub continuous_const
        have : Tendsto (fun y : K => y - x) (𝓝 x) (𝓝 (x - x)) := hcont.tendsto x
        rwa [sub_self] at this
      exact hc (hball x hx)
    filter_upwards [h1] with y hy
    exact Valuation.map_eq_of_sub_lt v hy
