/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.extensionFun_eq_zero_iff
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 292
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 2 (round 0 = first attempt)
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
  have hcont : Continuous v.restrict := by
    first
    | exact v.continuous_restrict
    | exact IsValuativeTopology.continuous_restrict v
    | exact IsValuativeTopology.continuous_restrict
    | exact Valuation.continuous_restrict v
    | exact v.restrict_continuous
    | exact v.continuous_restrict_of_compatible
    | fun_prop
  have hext : ∀ a : K, v.extensionFun (a : Completion K) = v.restrict a := by
    intro a
    first
    | exact Completion.isDenseInducing_coe.extend_eq hcont a
    | exact IsDenseInducing.extend_eq _ hcont a
    | (unfold extensionFun; exact IsDenseInducing.extend_eq _ hcont a)
  have hc : Continuous v.extensionFun := by
    first
    | exact v.continuous_extensionFun
    | exact Valuation.continuous_extensionFun v
    | exact v.extensionFun_continuous
    | fun_prop
  have hmul : ∀ a b : Completion K,
      v.extensionFun (a * b) = v.extensionFun a * v.extensionFun b := by
    intro a b
    refine Completion.induction_on₂ a b ?_ ?_
    · exact isClosed_eq (hc.comp continuous_mul)
        ((hc.comp continuous_fst).mul (hc.comp continuous_snd))
    · intro a b
      rw [← Completion.coe_mul, hext, hext, hext, map_mul]
  constructor
  · intro h
    by_contra hx
    have h1 : v.extensionFun x * v.extensionFun x⁻¹ = 1 := by
      rw [← hmul, mul_inv_cancel₀ hx, ← Completion.coe_one, hext, map_one]
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  · rintro rfl
    rw [← Completion.coe_zero, hext, map_zero]
