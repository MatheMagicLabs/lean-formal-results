/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.le_eLpNorm_of_bddBelow'
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/Monotonicity.lean, line 88
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
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
  by_cases hfm : AEStronglyMeasurable f μ
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hfm]; exact le_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp' hfm, one_div,
    ENNReal.le_rpow_inv_iff hp0,
    ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg, ← ENNReal.rpow_mul,
    inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one, ← setLIntegral_const]
  calc ∫⁻ _ in s, C ^ p.toReal ∂μ
      ≤ ∫⁻ x in s, ‖f x‖ₑ ^ p.toReal ∂μ := by
        apply setLIntegral_mono_ae ((hfm.enorm.pow_const _).restrict)
        filter_upwards [hf] with x hx hxs
        exact ENNReal.rpow_le_rpow (hx hxs) hp0.le
    _ ≤ ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ := setLIntegral_le_lintegral _ _
