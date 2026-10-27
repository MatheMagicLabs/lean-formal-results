/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.eLpNorm_const_mul_ennreal_of_pos
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/SMul.lean, line 167
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Filter
open scoped ENNReal NNReal Topology
namespace MeasureTheory
variable {α F : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ : Measure α}
section Lp
section IsBoundedSMul
variable {𝕜 : Type*} [NormedRing 𝕜] [MulActionWithZero 𝕜 F] [IsBoundedSMul 𝕜 F] {c : 𝕜}
end IsBoundedSMul
section ENormSMulClass
variable {𝕜 : Type*} [NormedRing 𝕜]
end ENormSMulClass
section ENormSMulClass
variable {𝕜 : Type*} [NormedRing 𝕜]
end ENormSMulClass
section NormedSpace
variable {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 F] [NormSMulClass 𝕜 F]
end NormedSpace
section ENNReal

theorem eLpNorm_const_mul_ennreal_of_pos {f : α → ℝ≥0∞} {c : ℝ≥0∞} (hp : 0 < p) :
    eLpNorm (fun x ↦ c * f x) p μ = c * eLpNorm f p μ := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hmeas (g : α → ℝ≥0∞) (a : ℝ≥0∞)
      (hg : AEStronglyMeasurable g μ) :
      eLpNorm (fun x ↦ a * g x) p μ = a * eLpNorm g p μ := by
    have hag : AEStronglyMeasurable (fun x ↦ a * g x) μ :=
      (aemeasurable_const.mul hg.aemeasurable).aestronglyMeasurable
    unfold eLpNorm
    simp only [hp0, if_false, hg, hag, if_true]
    by_cases hpt : p = ∞
    · simp only [hpt, if_true]
      change essSup (fun x ↦ a * g x) μ = a * essSup g μ
      exact ENNReal.essSup_const_mul
    · simp only [hpt, if_false]
      have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
      have hg' : AEMeasurable g μ := hg.aemeasurable
      have hpow : AEMeasurable (fun x ↦ g x ^ p.toReal) μ := by
        fun_prop
      change (∫⁻ x, (a * g x) ^ p.toReal ∂μ) ^ (1 / p.toReal) =
        a * (∫⁻ x, g x ^ p.toReal ∂μ) ^ (1 / p.toReal)
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hpr.le]
      rw [lintegral_const_mul'' _ hpow,
        ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hpr).le,
        ← ENNReal.rpow_mul]
      simp [hpr.ne']
  by_cases hf : AEStronglyMeasurable f μ
  · exact hmeas f c hf
  by_cases hc0 : c = 0
  · subst c
    simp
  by_cases hct : c = ∞
  · subst c
    have hr : (∞ : ℝ≥0∞) * eLpNorm f p μ = ∞ := by
      simp [eLpNorm, hp0, hf]
    rw [hr]
    by_cases hg : AEStronglyMeasurable (fun x ↦ ∞ * f x) μ
    · have hs := hmeas (fun x ↦ ∞ * f x) 2 hg
      have heq : (fun x ↦ (2 : ℝ≥0∞) * (∞ * f x)) =
          (fun x ↦ ∞ * f x) := by
        funext x
        rw [← mul_assoc]
        norm_num
      rw [heq] at hs
      have hreal := congrArg ENNReal.toReal hs
      rw [ENNReal.toReal_mul] at hreal
      norm_num at hreal
      have hzreal :
          (eLpNorm (fun x ↦ ∞ * f x) p μ).toReal = 0 := by
        linarith
      by_cases hz : eLpNorm (fun x ↦ ∞ * f x) p μ = 0
      · have hae : (fun x ↦ ∞ * f x) =ᵐ[μ] 0 := by
          simpa [eLpNorm_eq_zero_iff, hp0, hg] using hz
        have hfzero : f =ᵐ[μ] 0 := hae.mono fun x hx ↦ by
          simpa only [Pi.zero_apply, mul_eq_zero, ENNReal.top_ne_zero,
            false_or] using hx
        exact (hf (aestronglyMeasurable_const.congr hfzero.symm)).elim
      · by_contra ht
        exact (ne_of_gt (ENNReal.toReal_pos hz ht)) hzreal
    · simp [eLpNorm, hp0, hg]
  · have hcf : ¬AEStronglyMeasurable (fun x ↦ c * f x) μ := by
      intro hcf
      have hinv : AEStronglyMeasurable (fun x ↦ c⁻¹ * (c * f x)) μ :=
        (aemeasurable_const.mul hcf.aemeasurable).aestronglyMeasurable
      have hcancel : (fun x ↦ c⁻¹ * (c * f x)) = f := by
        funext x
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
      rw [hcancel] at hinv
      exact hf hinv
    simp [eLpNorm, hp0, hf, hcf, hc0]
