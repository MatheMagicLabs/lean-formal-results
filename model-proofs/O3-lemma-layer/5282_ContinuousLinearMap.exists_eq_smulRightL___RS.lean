/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ContinuousLinearMap.exists_eq_smulRightLₗ
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Operator/Bilinear.lean, line 494
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

suppress_compilation
open Filter hiding map_smul
open scoped NNReal Topology Uniformity
variable {𝕜 𝕜₂ 𝕜₃ E Eₗ E' Eₗ' F Fₗ F' Fₗ' G Gₗ G' Gₗ' : Type*}
section SemiNormed
open ContinuousLinearMap
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup Eₗ] [SeminormedAddCommGroup F]
variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
variable
namespace ContinuousLinearMap
section OpNorm
open Real
variable [RingHomIsometric σ₂₃]
open scoped ENNReal
end OpNorm
end ContinuousLinearMap
namespace LinearMap
variable [RingHomIsometric σ₂₃]
end LinearMap
namespace ContinuousLinearMap
variable [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃]
variable (E F G σ₁₃ σ₂₃)
variable {E F G σ₁₃ σ₂₃}
variable (𝕜 E Fₗ Gₗ)
variable {𝕜 E Fₗ Gₗ}
variable (F' σ₁₂)
variable [RingHomIsometric σ₁₂] [IsTopologicalAddGroup F'] [IsTopologicalAddGroup Fₗ']
variable {F' σ₁₂}
variable (𝕜 Fₗ')
variable {𝕜 Fₗ'}
variable (σ₁₂ σ₂₃ E F G E' F' G')
variable {σ₁₂ σ₂₃ E F G E' F' G'}
variable (𝕜 σ₁₂ σ₂₃ E E' Fₗ Fₗ' Gₗ Gₗ')
variable (Eₗ Eₗ') {𝕜 E E' Fₗ Fₗ' Gₗ Gₗ'}
variable [IsTopologicalAddGroup E']
end ContinuousLinearMap
namespace ContinuousLinearMap
variable {E'' F'' : Type*} [AddCommGroup E''] [AddCommGroup F'']
variable {𝕜₁' : Type*} {𝕜₂' : Type*} [NontriviallyNormedField 𝕜₁'] [NontriviallyNormedField 𝕜₂']
variable [RingHomIsometric σ₁₃] [RingHomIsometric σ₁'] [RingHomIsometric σ₂'] [IsNormableSpace 𝕜 E']
variable [IsTopologicalAddGroup Fₗ']
variable (𝕜 E' Fₗ')

private lemma exists_eq_smulRightLₗ :
    ∃ g : StrongDual 𝕜 E' →L[𝕜] Fₗ' →L[𝕜] E' →L[𝕜] Fₗ',
      ∀ a b, smulRightLₗ 𝕜 E' Fₗ' a b = g a b := by
  refine ⟨precompL E' ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (ContinuousLinearMap.id 𝕜 Fₗ')),
    fun a b => ?_⟩
  ext x
  first
    | (simp [precompL_apply]; done)
    | (rw [precompL_apply]; rfl)
    | rfl
