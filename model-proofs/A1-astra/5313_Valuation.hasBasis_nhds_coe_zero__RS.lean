/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.hasBasis_nhds_coe_zero
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 430
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 2 (round 0 = first attempt)
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

theorem hasBasis_nhds_coe_zero :
    (𝓝 (0 : Completion K)).HasBasis (fun _ ↦ True)
      fun γ : v.extension.ValueGroup₀ˣ ↦ {x | v.extension.restrict x < γ.1} := by
  have h : (𝓝 (0 : Completion K)).HasBasis (fun _ ↦ True)
      (fun γ : v.ValueGroup₀ˣ ↦
        {x : Completion K | v.extension x < embedding γ.1}) := by
    simpa only [Completion.coe_zero, v.closure_image_coe_ofPred_restrict_lt] using
      (v.hasBasis_nhds_zero.hasBasis_of_isDenseInducing
        Completion.isDenseInducing_coe)
  refine h.to_hasBasis ?_ ?_
  · intro γ _
    refine ⟨Units.map v.valueGroup₀ExtensionEquiv.toMonoidHom γ, trivial, ?_⟩
    intro x hx
    change v.extension.restrict x < v.valueGroup₀ExtensionEquiv γ.1 at hx
    rw [Valuation.restrict_lt_iff_lt_embedding,
      v.embedding_valueGroup₀ExtensionEquiv] at hx
    exact hx
  · intro γ _
    refine ⟨Units.map v.valueGroup₀ExtensionEquiv.symm.toMonoidHom γ, trivial, ?_⟩
    intro x hx
    change v.extension x < embedding (v.valueGroup₀ExtensionEquiv.symm γ.1) at hx
    rw [v.embedding_valueGroup₀ExtensionEquiv_symm] at hx
    change v.extension.restrict x < γ.1
    rw [Valuation.restrict_lt_iff_lt_embedding]
    exact hx
