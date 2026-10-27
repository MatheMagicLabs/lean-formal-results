/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ContinuousLinearMap.exists_eq_flip_toLinearMap
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Operator/Bilinear.lean, line 175
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 3 (round 0 = first attempt)
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

private lemma exists_eq_flip_toLinearMap (f : E' →SL[σ₁₃] F' →SL[σ₂₃] G') :
    ∃ g : F' →SL[σ₂₃] E' →SL[σ₁₃] G', ∀ a b, f.toLinearMap₁₂.flip a b = g a b := by
  letI := IsNormableSpace.toSeminormedAddCommGroup 𝕜 E'
  letI := IsNormableSpace.toNormedSpace 𝕜 E'
  letI := IsNormableSpace.toSeminormedAddCommGroup 𝕜₂ F'
  letI := IsNormableSpace.toNormedSpace 𝕜₂ F'
  letI := IsNormableSpace.toSeminormedAddCommGroup 𝕜₃ G'
  letI := IsNormableSpace.toNormedSpace 𝕜₃ G'
  have h : ∀ a b, ‖f b a‖ ≤ (‖f‖ * ‖a‖) * ‖b‖ := by
    intro a b
    calc
      ‖f b a‖ ≤ ‖f b‖ * ‖a‖ := (f b).le_opNorm a
      _ ≤ (‖f‖ * ‖b‖) * ‖a‖ :=
        mul_le_mul_of_nonneg_right (f.le_opNorm b) (norm_nonneg a)
      _ = (‖f‖ * ‖a‖) * ‖b‖ := by ring
  let g : F' →ₛₗ[σ₂₃] E' →SL[σ₁₃] G' :=
    { toFun := fun a =>
        (f.toLinearMap₁₂.flip a).mkContinuous (‖f‖ * ‖a‖) (h a)
      map_add' := by
        intro a b
        ext c
        change f c (a + b) = f c a + f c b
        exact (f c).map_add a b
      map_smul' := by
        intro r a
        ext b
        change f b (r • a) = σ₂₃ r • f b a
        exact (f b).map_smulₛₗ r a }
  refine ⟨g.mkContinuous ‖f‖ ?_, ?_⟩
  · intro a
    apply ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    intro b
    exact h a b
  · intro a b
    rfl
