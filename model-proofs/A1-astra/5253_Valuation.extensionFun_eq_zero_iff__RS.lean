/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.extensionFun_eq_zero_iff
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 292
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
    obtain ⟨z, hz, he⟩ := v.restrict.exists_eventually_map_eq hx
    letI : NeBot (Filter.comap ((↑) : K → Completion K) (𝓝 x)) := by
      first
      | exact Completion.isDenseInducing_coe.comap_nhds_neBot x
      | exact Completion.denseInducing_coe.comap_nhds_neBot x
    have ht :
        Tendsto (fun y : K => v.extensionFun (y : Completion K))
          (Filter.comap ((↑) : K → Completion K) (𝓝 x))
          (𝓝 (v.extensionFun x)) :=
      v.continuous_extensionFun.continuousAt.tendsto.comp tendsto_comap
    have he' :
        (fun y : K => v.extensionFun (y : Completion K)) =ᶠ[
          Filter.comap ((↑) : K → Completion K) (𝓝 x)]
        (fun _ => v.restrict z) := by
      filter_upwards [he] with y hy
      exact (v.extensionFun_extends y).trans hy
    have heq : v.extensionFun x = v.restrict z :=
      tendsto_nhds_unique ht (tendsto_const_nhds.congr' he'.symm)
    exact hz ((v.restrict.zero_iff).mp (heq.symm.trans h))
  · rintro rfl
    simpa using v.extensionFun_extends (0 : K)
