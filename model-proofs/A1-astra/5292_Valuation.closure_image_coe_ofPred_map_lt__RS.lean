/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.closure_image_coe_ofPred_map_lt
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 346
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

theorem closure_image_coe_ofPred_map_lt {r : Γ₀} (hr : r ≠ 0) :
    closure ((↑) '' {x : K | v x < r}) = {x : Completion K | v.extension x < r} := by
  ext x
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · subst x
      simpa using (pos_iff_ne_zero.mpr hr : 0 < r)
    · obtain ⟨y, hy, hy'⟩ :=
        mem_closure_iff_nhds.mp hx _ (v.extension_locally_const hx0)
      obtain ⟨z, hz, rfl⟩ := hy'
      have he : v z = v.extension x := by
        simpa only [Set.mem_setOf_eq, v.extension_apply_coe] using hy
      change v.extension x < r
      change v z < r at hz
      exact he ▸ hz
  · intro hx
    change v.extension x < r at hx
    apply mem_closure_iff_nhds.mpr
    intro U hU
    obtain ⟨z, hz, he⟩ := v.exists_coe_mem_extension_eq hU
    refine ⟨(z : Completion K), hz, z, ?_, rfl⟩
    change v z < r
    exact he ▸ hx
