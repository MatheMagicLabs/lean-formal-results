/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsNormableSpace.toPseudoMetrizableSpace
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/LocallyConvex/WithSeminorms.lean, line 611
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 3 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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

theorem IsNormableSpace.toPseudoMetrizableSpace : PseudoMetrizableSpace E := by
  have h := (IsNormableSpace.withSeminorms_seminorm (𝕜 := 𝕜) (E := E)).topologicalSpace_eq_iInf
  rw [iInf_const] at h
  obtain ⟨m, hmt⟩ : ∃ m : PseudoMetricSpace E,
      t = m.toUniformSpace.toTopologicalSpace := ⟨_, h⟩
  clear h
  subst hmt
  letI := m
  infer_instance
