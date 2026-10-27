/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.le_eLpNorm_of_bddBelow'
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/Monotonicity.lean, line 88
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 2 (round 0 = first attempt)
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
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp hp'
  by_cases hf' : AEStronglyMeasurable f μ
  · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp' hf']
    have h2 : μ s ≤ μ {x | C ^ p.toReal ≤ ‖f x‖ₑ ^ p.toReal} :=
      measure_mono_ae (hf.mono fun x hx hxs => ENNReal.rpow_le_rpow (hx hxs) hr.le)
    have h3 := mul_meas_ge_le_lintegral₀ (hf'.enorm.pow_const p.toReal) (C ^ p.toReal)
    have h4 : C ^ p.toReal * μ s ≤ ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ :=
      le_trans (mul_le_mul' le_rfl h2) h3
    calc C * μ s ^ (1 / p.toReal) = (C ^ p.toReal * μ s) ^ (1 / p.toReal) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
            mul_one_div_cancel hr.ne', ENNReal.rpow_one]
      _ ≤ (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) :=
          ENNReal.rpow_le_rpow h4 (by positivity)
  · first
    | simp [eLpNorm, eLpNorm', hp, hp', hf']
    | simp [eLpNorm, hp, hp', hf']
    | simp [eLpNorm_of_not_aestronglyMeasurable hf']
