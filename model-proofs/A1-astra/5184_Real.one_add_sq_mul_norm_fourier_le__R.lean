/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.one_add_sq_mul_norm_fourier_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Fourier/FourierTransformDeriv.lean, line 856
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  have hbound (g : ℝ → E) :
      ‖𝓕 g u‖ ≤ ∫ v, ‖g v‖ := by
    first
    | apply norm_fourier_le_integral_norm
    | apply VectorFourier.norm_fourierIntegral_le_integral_norm
    | apply norm_fourierIntegral_le_integral_norm
  have hder :
      𝓕 (iteratedDeriv 2 f) u =
        (2 * (π : ℂ) * I * (u : ℂ)) ^ 2 • 𝓕 f u := by
    have h :
        𝓕 (iteratedDeriv 2 f) =
          fun (x : ℝ) ↦
            (2 * (π : ℂ) * I * (x : ℂ)) ^ 2 • 𝓕 f x :=
      fourier_iteratedDeriv hf
        (fun n hn => h'f n (by exact_mod_cast hn)) (by norm_num)
    exact congrFun h u
  have hn :
      ‖(2 * (π : ℂ) * I * (u : ℂ)) ^ 2‖ =
        4 * π ^ 2 * u ^ 2 := by
    simp [norm_mul, norm_pow, Complex.norm_real,
      abs_of_pos pi_pos, mul_pow, sq_abs]
    <;> ring
    <;> simp
  have hd :
      (4 * π ^ 2) * u ^ 2 * ‖𝓕 f u‖ ≤
        ∫ v, ‖iteratedDeriv 2 f v‖ := by
    have h := hbound (iteratedDeriv 2 f)
    rwa [hder, norm_smul, hn] at h
  have hc : 0 < 4 * π ^ 2 := by positivity
  have hd' :
      u ^ 2 * ‖𝓕 f u‖ ≤
        (4 * π ^ 2)⁻¹ * ∫ v, ‖iteratedDeriv 2 f v‖ := by
    calc
      _ = (4 * π ^ 2)⁻¹ *
          ((4 * π ^ 2) * u ^ 2 * ‖𝓕 f u‖) := by
        rw [← mul_assoc, ← mul_assoc,
          inv_mul_cancel₀ (ne_of_gt hc), one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hc.le)
  nlinarith [hbound f]
