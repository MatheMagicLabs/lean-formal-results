/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsValuativeTopology.isClosedMap_restrict
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 157
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

lemma isClosedMap_restrict :
    IsClosedMap (v.restrict : K → v.ValueGroup₀) := by
  intro s hs
  apply WithZeroTopology.isClosed_iff.mpr
  by_cases h : (0 : K) ∈ s
  · exact Or.inl ⟨0, h, map_zero v.restrict⟩
  · right
    obtain ⟨γ, hγ⟩ :=
      (v.mem_nhds_zero_iff sᶜ).mp (hs.isOpen_compl.mem_nhds h)
    refine ⟨(γ : v.ValueGroup₀), Units.ne_zero γ, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    change (γ : v.ValueGroup₀) ≤ v.restrict x
    exact le_of_not_gt fun hlt => hγ hlt hx
