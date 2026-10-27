/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.extensionFun_eq_zero_iff
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 292
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

@[simp]
private lemma extensionFun_eq_zero_iff {x : Completion K} : v.extensionFun x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    have key : ∀ a b : Completion K,
        v.extensionFun (a * b) = v.extensionFun a * v.extensionFun b := by
      intro a b
      induction a, b using UniformSpace.Completion.induction_on₂ with
      | hp =>
        exact isClosed_eq (v.continuous_extensionFun.comp continuous_mul)
          ((v.continuous_extensionFun.comp continuous_fst).mul
            (v.continuous_extensionFun.comp continuous_snd))
      | ih a b =>
        rw [← UniformSpace.Completion.coe_mul, extensionFun_extends, extensionFun_extends,
          extensionFun_extends, map_mul]
    have := key x x⁻¹
    rw [mul_inv_cancel₀ hx, h, zero_mul, ← UniformSpace.Completion.coe_one,
      extensionFun_extends, map_one] at this
    exact one_ne_zero this
  · rintro rfl
    rw [← UniformSpace.Completion.coe_zero, extensionFun_extends, map_zero]
