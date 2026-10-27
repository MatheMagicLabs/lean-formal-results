/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.extensionFun_eq_zero_iff
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 292
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
end WithZeroTopology
end IsValuativeTopology
end DivisionRing
section Field
variable [Field K] [ValuativeRel K] [UniformSpace K] [IsValuativeTopology K]
namespace IsValuativeTopology
end IsValuativeTopology
namespace Valuation
variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) [v.Compatible]
open WithZeroTopology
variable [IsUniformAddGroup K]

@[simp]
private lemma extensionFun_eq_zero_iff {x : Completion K} : v.extensionFun x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra! hx
    obtain ⟨z₀, hz₀, hz₀'⟩ := v.exists_eventually_map_eq hx
    have h_restrict_eq : ∀ᶠ y in Filter.comap ((↑) : K → Completion K) (𝓝 x), v.restrict y = v.restrict z₀ := by
      filter_upwards [hz₀'] with y hy
      rw [v.restrict_inj]
      exact hy
    haveI : (Filter.comap ((↑) : K → Completion K) (𝓝 x)).NeBot :=
      Completion.isDenseInducing_coe.comap_nhds_neBot x
    have h_tendsto_restrict : Tendsto (v.restrict : K → v.ValueGroup₀)
        (Filter.comap ((↑) : K → Completion K) (𝓝 x)) (𝓝 0) := by
      have h_comp : (v.restrict : K → v.ValueGroup₀) = v.extensionFun ∘ (↑) := by
        ext y; exact (v.extensionFun_extends y).symm
      rw [h_comp]
      have h_cont : Tendsto v.extensionFun (𝓝 x) (𝓝 0) := by
        rw [← h]
        exact v.continuous_extensionFun.continuousAt.tendsto
      exact h_cont.comp tendsto_comap
    have h_tendsto_const : Tendsto (fun _ : K => v.restrict z₀)
        (Filter.comap ((↑) : K → Completion K) (𝓝 x)) (𝓝 (v.restrict z₀)) :=
      tendsto_const_nhds
    have h_tendsto_restrict' : Tendsto (v.restrict : K → v.ValueGroup₀)
        (Filter.comap ((↑) : K → Completion K) (𝓝 x)) (𝓝 (v.restrict z₀)) :=
      (tendsto_congr' h_restrict_eq).mpr h_tendsto_const
    have h_eq : (0 : v.ValueGroup₀) = v.restrict z₀ :=
      tendsto_nhds_unique h_tendsto_restrict h_tendsto_restrict'
    have h_restrict_z₀_ne_zero : v.restrict z₀ ≠ 0 := by
      rw [v.restrict.ne_zero_iff]
      exact hz₀
    exact h_restrict_z₀_ne_zero h_eq.symm
  · intro h
    rw [h]
    rw [← Completion.coe_zero, v.extensionFun_extends (0 : K), map_zero]
