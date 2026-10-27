/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.eLpNorm'_le_eLpNorm'_mul_eLpNorm'_of_enorm
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean, line 392
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Filter ENNReal
open scoped Topology
namespace MeasureTheory
section SameSpace
variable {α ε ε' : Type*} {m : MeasurableSpace α} {μ : Measure α} {f : α → ε}
end SameSpace
section Bilinear
variable {α E F G ε ε' ε'' : Type*} {m : MeasurableSpace α}
open NNReal

theorem eLpNorm'_le_eLpNorm'_mul_eLpNorm'_of_enorm {p q r : ℝ}
    (b : ε → ε' → ε'') (c : ℝ≥0∞) {f : α → ε} {g : α → ε'}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖ₑ ≤ c * ‖f x‖ₑ * ‖g x‖ₑ)
    (hpqr : Real.HolderTriple p q r) :
    eLpNorm' (fun x => b (f x) (g x)) r μ ≤ c * eLpNorm' f p μ * eLpNorm' g q μ := by
  have hp : 0 < p := hpqr.left_pos
  have hq : 0 < q := hpqr.right_pos
  have hsum : p⁻¹ + q⁻¹ = r⁻¹ := hpqr.inv_add_inv_eq_inv
  have hrinv : 0 < r⁻¹ := by
    rw [← hsum]; have := inv_pos.mpr hp; have := inv_pos.mpr hq; linarith
  have hr : 0 < r := inv_pos.mp hrinv
  rw [eLpNorm']
  calc
    (∫⁻ a : α, ‖b (f a) (g a)‖ₑ ^ r ∂μ) ^ (1 / r) ≤
        (∫⁻ a : α, (c * ‖f a‖ₑ * ‖g a‖ₑ) ^ r ∂μ) ^ (1 / r) :=
      (ENNReal.rpow_le_rpow_iff <| one_div_pos.mpr hr).mpr <|
        lintegral_mono_ae <| h.mono fun a ha => (ENNReal.rpow_le_rpow_iff hr).mpr <| ha
    _ = c * (∫⁻ a : α, (‖f a‖ₑ * ‖g a‖ₑ) ^ r ∂μ) ^ (1 / r) := by
      have key : ∀ a, (c * ‖f a‖ₑ * ‖g a‖ₑ) ^ r = c ^ r * (‖f a‖ₑ * ‖g a‖ₑ) ^ r :=
        fun a => by rw [mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ hr.le]
      simp_rw [key]
      have hm : AEMeasurable (fun a => (‖f a‖ₑ * ‖g a‖ₑ) ^ r) μ :=
        (hf.enorm.mul hg.enorm).pow_const r
      rw [lintegral_const_mul'' _ hm,
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 / r),
        ← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one]
    _ ≤ c * eLpNorm' f p μ * eLpNorm' g q μ := by
      rw [mul_assoc]
      gcongr
      rw [eLpNorm', eLpNorm']
      first
        | exact ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr hpqr μ hf.enorm hg.enorm
        | exact ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr hpqr hf.enorm hg.enorm
