/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ContinuousLinearMap.exists_eq_flip_toLinearMap
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Operator/Bilinear.lean, line 175
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
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
  first
  | letI := IsNormableSpace.toSeminormedAddCommGroup 𝕜 E'
  | letI := IsNormableSpace.seminormedAddCommGroup 𝕜 E'
  first
  | letI := IsNormableSpace.toNormedSpace 𝕜 E'
  | letI := IsNormableSpace.normedSpace 𝕜 E'
  first
  | letI := IsNormableSpace.toSeminormedAddCommGroup 𝕜₂ F'
  | letI := IsNormableSpace.seminormedAddCommGroup 𝕜₂ F'
  first
  | letI := IsNormableSpace.toNormedSpace 𝕜₂ F'
  | letI := IsNormableSpace.normedSpace 𝕜₂ F'
  first
  | letI := IsNormableSpace.toSeminormedAddCommGroup 𝕜₃ G'
  | letI := IsNormableSpace.seminormedAddCommGroup 𝕜₃ G'
  first
  | letI := IsNormableSpace.toNormedSpace 𝕜₃ G'
  | letI := IsNormableSpace.normedSpace 𝕜₃ G'
  let L := f.toLinearMap₁₂.flip
  have h (b : F') (a : E') : ‖L b a‖ ≤ (‖f‖ * ‖b‖) * ‖a‖ := by
    change ‖f a b‖ ≤ (‖f‖ * ‖b‖) * ‖a‖
    calc
      ‖f a b‖ ≤ ‖f a‖ * ‖b‖ := (f a).le_opNorm b
      _ ≤ (‖f‖ * ‖a‖) * ‖b‖ :=
        mul_le_mul_of_nonneg_right (f.le_opNorm a) (norm_nonneg b)
      _ = (‖f‖ * ‖b‖) * ‖a‖ := by ring
  let g : F' →ₛₗ[σ₂₃] E' →SL[σ₁₃] G' :=
    { toFun := fun b => (L b).mkContinuous (‖f‖ * ‖b‖) (h b)
      map_add' := by
        intro b c
        ext a
        exact congrArg (fun k : E' →ₛₗ[σ₁₃] G' => k a) (L.map_add b c)
      map_smul' := by
        intro c b
        ext a
        exact congrArg (fun k : E' →ₛₗ[σ₁₃] G' => k a) (L.map_smulₛₗ c b) }
  refine ⟨g.mkContinuous ‖f‖ ?_, ?_⟩
  · intro b
    apply ContinuousLinearMap.opNorm_le_bound (g b)
      (mul_nonneg (norm_nonneg f) (norm_nonneg b))
    intro a
    exact h b a
  · intro a b
    rfl
