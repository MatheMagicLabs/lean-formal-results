/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.closure_image_coe_ofPred_map_lt
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 346
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 0 (round 0 = first attempt)
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
    have hc : IsClosed {x : Completion K | v.extension x < r} := by
      rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro y hy
      simp only [mem_compl_iff, mem_setOf_eq, not_lt] at hy
      have hy0 : y ≠ 0 := by
        rintro rfl
        have h' := hy
        rw [map_zero] at h'
        exact hr (le_antisymm h' zero_le')
      filter_upwards [v.extension_locally_const hy0] with z hz
      simp only [mem_compl_iff, mem_setOf_eq, not_lt]
      have hz' : v.extension z = v.extension y := hz
      rw [hz']
      exact hy
    refine closure_minimal ?_ hc hx
    rintro _ ⟨y, hy, rfl⟩
    simpa [v.extension_apply_coe] using hy
  · intro hx
    by_cases h0 : x = 0
    · subst h0
      apply subset_closure
      exact ⟨0, by simpa [zero_lt_iff] using hr, by simp⟩
    · rw [mem_closure_iff_nhds]
      intro U hU
      obtain ⟨_, ⟨y, rfl⟩, hyU, hyc⟩ :=
        (UniformSpace.Completion.denseRange_coe (α := K)).inter_nhds_nonempty
          (inter_mem hU (v.extension_locally_const h0))
      refine ⟨_, hyU, y, ?_, rfl⟩
      have hyc' : v.extension (y : Completion K) = v.extension x := hyc
      show v y < r
      rw [← v.extension_apply_coe, hyc']
      exact hx
