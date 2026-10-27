/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.one_add_sq_mul_norm_fourier_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Fourier/FourierTransformDeriv.lean, line 856
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  have h1 : ∀ g : ℝ → E, ‖𝓕 g u‖ ≤ ∫ v, ‖g v‖ := by
    intro g
    first
    | exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    | exact Real.norm_fourier_le_integral_norm g u
    | exact Real.norm_fourierIntegral_le_integral_norm g u
    | (refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_); simp [Circle.norm_smul])
  have h2 := h1 (iteratedDeriv 2 f)
  have hF : 𝓕 (iteratedDeriv 2 f) u = (2 * π * I * u) ^ 2 • 𝓕 f u := by
    first
    | rw [Real.fourier_iteratedDeriv (N := 2) (n := 2) hf
        (fun k hk => h'f k (by exact_mod_cast hk)) (by norm_num)]
    | rw [Real.fourierIntegral_iteratedDeriv (N := 2) (n := 2) hf
        (fun k hk => h'f k (by exact_mod_cast hk)) (by norm_num)]
  have hn : ‖(2 * π * I * u : ℂ)‖ = 2 * π * |u| := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos]
  have h3 : ‖𝓕 (iteratedDeriv 2 f) u‖ = 4 * π ^ 2 * u ^ 2 * ‖𝓕 f u‖ := by
    rw [hF, norm_smul, norm_pow, hn, mul_pow, mul_pow, sq_abs]
    ring
  have hpi := pi_pos.ne'
  have h4 : u ^ 2 * ‖𝓕 f u‖ ≤ (4 * π ^ 2)⁻¹ * ∫ v, ‖iteratedDeriv 2 f v‖ := by
    calc u ^ 2 * ‖𝓕 f u‖ = (4 * π ^ 2)⁻¹ * (4 * π ^ 2 * u ^ 2 * ‖𝓕 f u‖) := by
          field_simp
      _ ≤ (4 * π ^ 2)⁻¹ * ∫ v, ‖iteratedDeriv 2 f v‖ :=
          mul_le_mul_of_nonneg_left (by rw [← h3]; exact h2) (by positivity)
  have h5 := h1 f
  rw [add_mul, one_mul]
  linarith
