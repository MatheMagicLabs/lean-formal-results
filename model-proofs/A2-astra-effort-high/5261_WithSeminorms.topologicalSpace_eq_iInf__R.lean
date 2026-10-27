/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     WithSeminorms.topologicalSpace_eq_iInf
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/LocallyConvex/WithSeminorms.lean, line 506
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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

theorem WithSeminorms.topologicalSpace_eq_iInf
    {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) :
    t = ⨅ i, (p i).toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace := by
  apply TopologicalSpace.ext_nhds
  intro x
  rw [nhds_iInf]
  have h (l : Filter E) :
      l ≤ @nhds E t x ↔
        ∀ i, Tendsto (fun y => p i (y - x)) l (𝓝 (0 : ℝ)) := by
    change Tendsto id l (𝓝 x) ↔ _
    rw [hp.tendsto_nhds id x]
    apply forall_congr'
    intro i
    have habs (y : E) : |p i (y - x)| = p i (y - x) :=
      abs_of_nonneg (by positivity)
    simp only [Metric.tendsto_nhds, Real.dist_eq, sub_zero, habs, id_eq]
  have hi (i : ι) (l : Filter E) :
      l ≤ @nhds E
          (p i).toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace x ↔
        Tendsto (fun y => p i (y - x)) l (𝓝 (0 : ℝ)) := by
    letI := (p i).toSeminormedAddCommGroup
    change Tendsto id l (@nhds E
      (p i).toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace x) ↔ _
    exact tendsto_iff_norm_sub_tendsto_zero
  apply le_antisymm
  · exact le_iInf fun i => (hi i _).2 ((h _).1 le_rfl i)
  · apply (h _).2
    intro i
    exact (hi i _).1 (iInf_le _ i)
