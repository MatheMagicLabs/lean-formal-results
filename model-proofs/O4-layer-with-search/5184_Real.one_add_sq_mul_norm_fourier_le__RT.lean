/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.one_add_sq_mul_norm_fourier_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Fourier/FourierTransformDeriv.lean, line 856
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
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
  have h1 := norm_fourier_le_integral_norm f u
  have h2 := norm_fourier_le_integral_norm (iteratedDeriv 2 f) u
  have hF := fourier_iteratedDeriv (N := 2) (n := 2) (f := f) (by exact_mod_cast hf)
    (fun n hn => h'f n (by exact_mod_cast hn)) le_rfl
  rw [hF] at h2
  have key : ‖(2 * (π : ℂ) * I * (u : ℂ)) ^ 2‖ = 4 * π ^ 2 * u ^ 2 := by
    have : (2 * (π : ℂ) * I * (u : ℂ)) ^ 2 = -((4 * π ^ 2 * u ^ 2 : ℝ) : ℂ) := by
      push_cast
      linear_combination (4 * (π : ℂ) ^ 2 * (u : ℂ) ^ 2) * I_sq
    rw [this, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  simp only at h2
  rw [norm_smul, key] at h2
  have hpi : 0 < 4 * π ^ 2 := by positivity
  have h3 : u ^ 2 * ‖𝓕 f u‖ ≤ (4 * π ^ 2)⁻¹ * ∫ v, ‖iteratedDeriv 2 f v‖ := by
    rw [le_inv_mul_iff₀ hpi]
    linarith [h2]
  rw [add_mul, one_mul]
  linarith
