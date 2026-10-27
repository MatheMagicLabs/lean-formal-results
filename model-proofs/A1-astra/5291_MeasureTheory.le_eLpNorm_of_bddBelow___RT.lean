/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.le_eLpNorm_of_bddBelow'
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/Monotonicity.lean, line 88
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  by_cases hfm : AEStronglyMeasurable f μ
  · have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp hp'
    have hle : C ^ p.toReal * μ s ≤ ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ := by
      calc
        C ^ p.toReal * μ s = ∫⁻ _ in s, C ^ p.toReal ∂μ :=
          (setLIntegral_const s _).symm
        _ ≤ ∫⁻ x in s, ‖f x‖ₑ ^ p.toReal ∂μ := by
          apply setLIntegral_mono_ae (hfm.enorm.pow_const _).restrict
          filter_upwards [hf] with x hx
          intro hxs
          exact ENNReal.rpow_le_rpow (hx hxs) hp_pos.le
        _ ≤ ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ :=
          setLIntegral_le_lintegral _ _
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp' hfm]
    have h := ENNReal.rpow_le_rpow hle (one_div_nonneg.mpr hp_pos.le)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp_pos.le)] at h
    rw [← ENNReal.rpow_mul, one_div, mul_inv_cancel₀ hp_pos.ne',
      ENNReal.rpow_one] at h
    simpa only [one_div] using h
  · rw [eLpNorm_of_not_aestronglyMeasurable hfm]
    exact le_top
