/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.one_add_sq_mul_norm_fourier_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Fourier/FourierTransformDeriv.lean, line 856
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

noncomputable section
open Real Complex MeasureTheory Filter TopologicalSpace
open scoped FourierTransform Topology ContDiff
attribute [local instance 101] secondCountableTopologyEither_of_left
namespace Real
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
end Real
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace VectorFourier
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
set_option backward.isDefEq.respectTransparency false in
variable {f}
open ContinuousMultilinearMap
variable [MeasurableSpace V] [BorelSpace V] {μ : Measure V}
section SecondCountableTopology
variable [SecondCountableTopology V]
end SecondCountableTopology
end VectorFourier
namespace Real
open VectorFourier
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem one_add_sq_mul_norm_fourier_le {f : ℝ → E} (hf : ContDiff ℝ 2 f)
    (h'f : ∀ k ≤ 2, Integrable (iteratedDeriv k f)) (u : ℝ) :
    (1 + u ^ 2) * ‖𝓕 f u‖ ≤
      (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * ∫ v, ‖iteratedDeriv 2 f v‖ := by
  have hbound (g : ℝ → E) : ‖𝓕 g u‖ ≤ ∫ v, ‖g v‖ := by
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    simp
  have htwo :
      (4 * π ^ 2) * (u ^ 2 * ‖𝓕 f u‖) ≤
        ∫ v, ‖iteratedDeriv 2 f v‖ := by
    calc
      (4 * π ^ 2) * (u ^ 2 * ‖𝓕 f u‖) =
          ‖𝓕 (iteratedDeriv 2 f) u‖ := by
        rw [fourier_iteratedDeriv hf
          (fun n hn => h'f n (by exact_mod_cast hn))] <;>
          simp [norm_smul, norm_mul, norm_pow, mul_pow, Real.norm_eq_abs] <;>
          ring
      _ ≤ _ := hbound _
  have hc : 0 < 4 * π ^ 2 := by positivity
  have htwo' :=
    mul_le_mul_of_nonneg_left htwo (inv_nonneg.mpr hc.le)
  simp only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at htwo'
  nlinarith [hbound f]
