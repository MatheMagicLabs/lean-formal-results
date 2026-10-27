/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsValuativeTopology.continuous_valuation_of_surjective
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 142
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA3-leanstral-agent-feedback, arm rueck, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent with goal-state feedback (arm rueck)
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
  · -- case v x = 0, need to show continuity at 0
    rw [continuousAt_def, hx, WithZeroTopology.nhds_zero]
    -- need: Tendsto v (𝓝 x) (⨅ γ ≠ 0, 𝓟 (Iio γ))
    -- where ⨅ γ ≠ 0, 𝓟 (Iio γ) means ⨅ (γ : Γ₀), ⨅ (h : γ ≠ 0), 𝓟 (Iio γ)
    refine tendsto_iInf.2 fun γ ↦ ?_
    refine tendsto_iInf.2 fun hγ ↦ ?_
    -- hγ : γ ≠ 0
    -- Need: Tendsto v (𝓝 x) (𝓟 (Iio γ))
    rw [tendsto_principal]
    -- Need: ∀ᶠ a in 𝓝 x, v a ∈ Iio γ, i.e., v a < γ
    -- Since v is surjective, pick z such that v z = γ
    obtain ⟨z, hz⟩ := hsurj γ
    have hz_restrict_ne_zero : v.restrict z ≠ 0 :=
      mt (Valuation.restrict_eq_zero_iff (v := v) (x := z)).mp (by rwa [hz])
    -- Show that v⁻¹' (Iio γ) ∈ 𝓝 x using the basis
    have hmem : v ⁻¹' (Iio γ) ∈ 𝓝 x := by
      have basis := v.hasBasis_nhds x
      rw [basis.mem_iff]
      -- Need to find a unit r such that the basis set is contained in v⁻¹' (Iio γ)
      let r : v.ValueGroup₀ˣ := Units.mk0 (v.restrict z) hz_restrict_ne_zero
      refine ⟨r, trivial, ?_⟩
      intro y hy
      -- hy : v.restrict (y - x) < r.val = v.restrict z
      -- Need: y ∈ v⁻¹' (Iio γ), i.e., v y < γ = v z
      -- i.e., v.restrict y < v.restrict z
      have hle : v.restrict y ≤ v.restrict (y - x) := by
        calc
          v.restrict y = v.restrict ((y - x) + x) := by rw [sub_add_cancel]
          _ ≤ max (v.restrict (y - x)) (v.restrict x) := v.restrict.map_add _ _
          _ = max (v.restrict (y - x)) 0 := by
            rw [(Valuation.restrict_eq_zero_iff (v := v) (x := x)).mpr hx]
          _ = v.restrict (y - x) := by simp
      have hlt : v.restrict y < v.restrict z := hle.trans_lt hy
      -- Need: y ∈ v⁻¹' (Iio γ), i.e., v y < γ
      -- v.restrict y < v.restrict z ↔ v y < v z ↔ v y < γ
      have hy_lt : v y < γ := by
        -- hlt: v.restrict y < v.restrict z
        -- Using restrict_lt_iff: v.restrict y < v.restrict z ↔ v y < v z
        have := (v.restrict_lt_iff (x := y) (y := z)).mp hlt
        rwa [hz] at this
      exact hy_lt
    -- Convert to the filter goal
    exact hmem
  · -- case v x ≠ 0, use locally_const
    exact Filter.EventuallyEq.continuousAt (y := v x) (v.locally_const hx)
