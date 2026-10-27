/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Topology.IsInducing.isNormableSpace
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/LocallyConvex/WithSeminorms.lean, line 1163
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open NormedField Set Seminorm TopologicalSpace Filter List Bornology
open NNReal Pointwise Topology Uniformity
variable {R 𝕜 𝕜₂ 𝕝 𝕝₂ E F G ι ι' : Type*}
section FilterBasis
variable [SeminormedRing R] [AddCommGroup E] [Module R E]
variable (R E ι)
variable {R E ι}
namespace SeminormFamily
variable (p : SeminormFamily R E ι)
variable [NormedDivisionRing 𝕜] [AddCommGroup F] [Module 𝕜 F] (p : SeminormFamily 𝕜 F ι)
end SeminormFamily
end FilterBasis
section Bounded
namespace Seminorm
variable [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [SeminormedRing 𝕜₂] [AddCommGroup F] [Module 𝕜₂ F]
variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]
end Seminorm
end Bounded
section Topology
variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable (𝕜 E) in
variable (𝕜 E) in
variable [TopologicalSpace E]
variable {p : SeminormFamily 𝕜 E ι}
variable (𝕜 E) in
variable (𝕜 E) in
variable (𝕜 E) in
variable (𝕜 E) in
end Topology
section Tendsto
variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {p : SeminormFamily 𝕜 E ι}
variable [SemilatticeSup F] [Nonempty F]
end Tendsto
section IsTopologicalAddGroup
variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
section TopologicalSpace
variable [t : TopologicalSpace E]
end TopologicalSpace
end IsTopologicalAddGroup
section NormedSpace
variable [NormedField 𝕜] [ha : AddCommGroup E] [hm : Module 𝕜 E]
variable (𝕜 E)
end NormedSpace
section NontriviallyNormedField
variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable {p : SeminormFamily 𝕜 E ι}
variable [TopologicalSpace E]
end NontriviallyNormedField
section continuous_of_bounded
namespace WithSeminorms
variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [NormedField 𝕝] [Module 𝕝 E]
variable [NormedField 𝕜₂] [AddCommGroup F] [Module 𝕜₂ F]
variable [NormedField 𝕝₂] [Module 𝕝₂ F]
variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]
variable {τ₁₂ : 𝕝 →+* 𝕝₂} [RingHomIsometric τ₁₂]
end WithSeminorms
section Congr
namespace WithSeminorms
variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [SeminormedRing 𝕜₂] [AddCommGroup F] [Module 𝕜₂ F]
end WithSeminorms
end Congr
end continuous_of_bounded
section bounded_of_continuous
namespace Seminorm
variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
end Seminorm
end bounded_of_continuous
section LocallyConvexSpace
open LocallyConvexSpace
variable [NormedField 𝕜] [NormedSpace ℝ 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
end LocallyConvexSpace
section NormedSpace
variable (𝕜) [NormedField 𝕜] [NormedSpace ℝ 𝕜] [SeminormedAddCommGroup E]
end NormedSpace
section TopologicalConstructions
variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [NormedField 𝕜₂] [AddCommGroup F] [Module 𝕜₂ F]
variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]
variable [TopologicalSpace F]

theorem Topology.IsInducing.isNormableSpace [h : IsNormableSpace 𝕜₂ F]
    [TopologicalSpace E] {f : E →ₛₗ[σ₁₂] F} (hf : IsInducing f) :
    IsNormableSpace 𝕜 E := by
  letI := IsNormableSpace.toSeminormedAddCommGroup 𝕜₂ F
  letI := IsNormableSpace.toNormedSpace 𝕜₂ F
  let s := SeminormedAddCommGroup.induced E F f
  letI : SeminormedAddCommGroup E :=
    { s with
      toPseudoMetricSpace := s.toPseudoMetricSpace.replaceTopology hf.eq_induced }
  letI : NormedSpace 𝕜 E :=
    { norm_smul_le := fun c x => by
        change ‖f (c • x)‖ ≤ ‖c‖ * ‖f x‖
        simpa using norm_smul_le (σ₁₂ c) (f x) }
  infer_instance
