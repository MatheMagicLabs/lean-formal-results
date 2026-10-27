/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.extensionFun_extends
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 211
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

@[simp, norm_cast]
private theorem extensionFun_extends (x : K) :
    v.extensionFun (x : Completion K) = v.restrict x := by
  unfold Valuation.extensionFun
  first
  | (refine UniformSpace.Completion.isDenseInducing_coe.extend_eq_of_tendsto ?_
     rw [← UniformSpace.Completion.isDenseInducing_coe.nhds_eq_comap]
     exact (IsValuativeTopology.continuous_restrict v).continuousAt)
  | (refine IsDenseInducing.extend_eq_of_tendsto _ ?_
     rw [← UniformSpace.Completion.isDenseInducing_coe.nhds_eq_comap]
     exact (IsValuativeTopology.continuous_restrict v).continuousAt)
  | (rw [UniformSpace.Completion.extension_coe]
     exact uniformContinuous_of_continuousAt_zero _ (IsValuativeTopology.continuous_restrict v).continuousAt)
