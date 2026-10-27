/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.extensionFun_eq_zero_iff
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 292
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
    by_contra hx
    obtain ⟨z₀, hz₀, hev⟩ := v.exists_eventually_map_eq hx
    haveI : (Filter.comap ((↑) : K → Completion K) (𝓝 x)).NeBot :=
      (UniformSpace.Completion.isDenseInducing_coe (α := K)).comap_nhds_neBot x
    have h1 : Tendsto (fun y : K => v.extensionFun (y : Completion K))
        (Filter.comap ((↑) : K → Completion K) (𝓝 x)) (𝓝 (v.extensionFun x)) :=
      (v.continuous_extensionFun.tendsto x).comp Filter.tendsto_comap
    have h2 : Tendsto (fun y : K => v.extensionFun (y : Completion K))
        (Filter.comap ((↑) : K → Completion K) (𝓝 x)) (𝓝 (v.restrict z₀)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with y hy
      rw [v.extensionFun_extends]
      first
        | simp [hy]
        | simp [Valuation.restrict, hy]
        | simp [Valuation.restrict_def, hy]
        | (simp only [Valuation.restrict]; rw [hy])
    have h3 := tendsto_nhds_unique h1 h2
    rw [h] at h3
    first
      | exact hz₀ ((v.zero_iff).1 ((v.restrict_eq_zero_iff).1 h3.symm))
      | exact hz₀ (by simpa using h3.symm)
      | simp at h3; exact hz₀ (by simpa using h3.symm)
  · rintro rfl
    have := v.extensionFun_extends 0
    simpa using this
