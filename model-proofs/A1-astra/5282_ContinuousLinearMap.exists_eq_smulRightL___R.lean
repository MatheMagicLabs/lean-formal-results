/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ContinuousLinearMap.exists_eq_smulRightLₗ
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Operator/Bilinear.lean, line 494
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  first
  | letI := IsNormableSpace.toSeminormedAddCommGroup 𝕜 E'
  | letI := IsNormableSpace.toNormedAddCommGroup 𝕜 E'
  | letI := IsNormableSpace.seminormedAddCommGroup 𝕜 E'
  | letI := IsNormableSpace.normedAddCommGroup 𝕜 E'
  first
  | letI := IsNormableSpace.toNormedSpace 𝕜 E'
  | letI := IsNormableSpace.normedSpace 𝕜 E'
  first
  | letI := IsNormableSpace.toSeminormedAddCommGroup 𝕜 Fₗ'
  | letI := IsNormableSpace.toNormedAddCommGroup 𝕜 Fₗ'
  | letI := IsNormableSpace.seminormedAddCommGroup 𝕜 Fₗ'
  | letI := IsNormableSpace.normedAddCommGroup 𝕜 Fₗ'
  first
  | letI := IsNormableSpace.toNormedSpace 𝕜 Fₗ'
  | letI := IsNormableSpace.normedSpace 𝕜 Fₗ'
  refine ⟨LinearMap.mkContinuous₂ (smulRightLₗ 𝕜 E' Fₗ') 1 ?_, ?_⟩
  · intro a b
    simp only [one_mul]
    apply ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (norm_nonneg a) (norm_nonneg b))
    intro x
    change ‖a x • b‖ ≤ ‖a‖ * ‖b‖ * ‖x‖
    calc
      ‖a x • b‖ = ‖a x‖ * ‖b‖ := norm_smul _ _
      _ ≤ (‖a‖ * ‖x‖) * ‖b‖ :=
        mul_le_mul_of_nonneg_right (a.le_opNorm x) (norm_nonneg b)
      _ = ‖a‖ * ‖b‖ * ‖x‖ := by ring
  · intro a b
    rfl
