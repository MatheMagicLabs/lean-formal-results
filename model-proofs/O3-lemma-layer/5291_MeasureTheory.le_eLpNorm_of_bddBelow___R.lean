/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.le_eLpNorm_of_bddBelow'
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/Monotonicity.lean, line 88
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 3 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open TopologicalSpace MeasureTheory Filter
open scoped NNReal ENNReal ComplexConjugate
variable {α E F G : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ : Measure α}
namespace MeasureTheory
section Monotonicity
variable {ε ε' : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
section ESeminormedAddMonoid
variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]

theorem le_eLpNorm_of_bddBelow' (hp : p ≠ 0) (hp' : p ≠ ∞) {f : α → ε} (C : ℝ≥0∞) {s : Set α}
    (hf : ∀ᵐ x ∂μ, x ∈ s → C ≤ ‖f x‖ₑ) :
    C * μ s ^ (1 / p.toReal) ≤ eLpNorm f p μ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos hp hp'
  rw [eLpNorm, if_neg hp, if_neg hp', eLpNorm', one_div]
  split_ifs with hfm
  · have hmeas : AEMeasurable (fun x => ‖f x‖ₑ ^ p.toReal) μ := by
      first
      | exact hfm.enorm.pow_const _
      | exact (hfm.enorm).pow_const p.toReal
      | exact hfm.aemeasurable.enorm.pow_const _
    have hst : s ≤ᵐ[μ] {x | C ^ p.toReal ≤ ‖f x‖ₑ ^ p.toReal} := by
      filter_upwards [hf] with x hx hxs
      exact ENNReal.rpow_le_rpow (hx hxs) ENNReal.toReal_nonneg
    have hμ : μ s ≤ μ {x | C ^ p.toReal ≤ ‖f x‖ₑ ^ p.toReal} := measure_mono_ae hst
    have h : C ^ p.toReal * μ s ≤ ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ := by
      calc C ^ p.toReal * μ s
          ≤ C ^ p.toReal * μ {x | C ^ p.toReal ≤ ‖f x‖ₑ ^ p.toReal} := by
            first
            | exact mul_le_mul_left' hμ _
            | exact mul_le_mul' le_rfl hμ
        _ ≤ ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ := mul_meas_ge_le_lintegral₀ hmeas _
    calc C * μ s ^ p.toReal⁻¹ = (C ^ p.toReal * μ s) ^ p.toReal⁻¹ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hp0.le), ← ENNReal.rpow_mul,
            mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one]
      _ ≤ (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ p.toReal⁻¹ :=
          ENNReal.rpow_le_rpow h (inv_nonneg.2 hp0.le)
  · exact le_top
