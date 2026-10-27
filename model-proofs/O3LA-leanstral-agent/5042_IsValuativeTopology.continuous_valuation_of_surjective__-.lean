/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsValuativeTopology.continuous_valuation_of_surjective
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 142
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA-leanstral-agent, arm -, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 as a tool-using agent (Mistral Vibe)
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
  · rw [ContinuousAt, hx, WithZeroTopology.nhds_zero]
    refine le_iInf₂ fun γ hγ => ?_
    obtain ⟨y, hy⟩ := hsurj γ
    have hy_ne : v y ≠ 0 := by rw [hy]; exact hγ
    have h_restrict_ne : v.restrict y ≠ 0 := by
      simpa [hy_ne] using (v.restrict_eq_zero_iff.not.mpr hy_ne)
    have hmem : {z | v (z - x) < γ} ∈ 𝓝 x := by
      rw [v.mem_nhds_iff]
      use Units.mk0 (v.restrict y) h_restrict_ne
      intro z hz
      simp only [Set.mem_setOf_eq, Units.val_mk0] at hz ⊢
      rw [v.restrict_lt_iff] at hz
      simpa [hy] using hz
    have hpre : v⁻¹' (Iio γ) ∈ 𝓝 x := by
      apply mem_of_superset hmem
      intro z hz
      have hle : v z ≤ v (z - x) := by
        calc
          v z = v ((z - x) + x) := by simp
          _ ≤ max (v (z - x)) (v x) := v.map_add _ _
          _ = max (v (z - x)) 0 := by rw [hx]
          _ = v (z - x) := by simp
      exact lt_of_le_of_lt hle hz
    simpa [Set.mem_preimage] using hpre
  · exact continuousAt_valuation_of_ne_zero v hx
