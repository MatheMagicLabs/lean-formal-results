/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.integrableOn_log_log_mul_rpow
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Gamma/Deriv.lean, line 170
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Filter Set Real Asymptotics
open scoped Topology
namespace Complex
section GammaHasDeriv
end GammaHasDeriv
end Complex
namespace Real
open Complex MeasureTheory

theorem integrableOn_log_log_mul_rpow {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t ↦ log (log t) * t ^ (-s)) (Ioi 1) := by
  let a : ℝ := s - 1
  have ha : 0 < a := sub_pos.mpr hs
  have hp : IntegrableOn
      (fun x : ℝ ↦ x ^ (1 / 2 : ℝ) * exp (-x)) (Ioi 0) := by
    simpa only [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num, mul_comm] using
      (GammaIntegral_convergent (s := (3 / 2 : ℝ)) (by norm_num))
  have hn : IntegrableOn
      (fun x : ℝ ↦ x ^ (-(1 / 2 : ℝ)) * exp (-x)) (Ioi 0) := by
    simpa only [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, mul_comm] using
      (GammaIntegral_convergent (s := (1 / 2 : ℝ)) (by norm_num))
  have he : IntegrableOn (fun x : ℝ ↦ exp (-x)) (Ioi 0) := by
    simpa only [sub_self, rpow_zero, mul_one] using
      (GammaIntegral_convergent (s := (1 : ℝ)) (by norm_num))
  have hl : IntegrableOn (fun x : ℝ ↦ log x * exp (-x)) (Ioi 0) := by
    refine ((hp.add hn).const_mul 2).mono' ?_ ?_
    · exact (measurable_log.mul
        (measurable_exp.comp measurable_neg)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have h₁ := log_le_sub_one_of_pos
        (rpow_pos_of_pos hx (1 / 2 : ℝ))
      have h₂ := log_le_sub_one_of_pos
        (rpow_pos_of_pos hx (-(1 / 2 : ℝ)))
      rw [log_rpow hx] at h₁ h₂
      have hb : |log x| ≤
          2 * (x ^ (1 / 2 : ℝ) + x ^ (-(1 / 2 : ℝ))) := by
        have hp' := rpow_pos_of_pos hx (1 / 2 : ℝ)
        have hn' := rpow_pos_of_pos hx (-(1 / 2 : ℝ))
        exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
      change ‖log x * exp (-x)‖ ≤
        2 * (x ^ (1 / 2 : ℝ) * exp (-x) +
          x ^ (-(1 / 2 : ℝ)) * exp (-x))
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos (-x))]
      nlinarith [mul_le_mul_of_nonneg_right hb (exp_pos (-x)).le]
  have hg : IntegrableOn
      (fun x : ℝ ↦ (log x - log a) * exp (-x) / a) (Ioi 0) := by
    unfold IntegrableOn
    simpa only [Pi.sub_apply, sub_mul] using
      (hl.sub (he.const_mul (log a))).div_const a
  have himage : (fun t : ℝ ↦ a * log t) '' Ioi 1 = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact mul_pos ha (log_pos ht)
    · intro hx
      refine ⟨exp (x / a), ?_, ?_⟩
      · change 1 < exp (x / a)
        rw [← exp_zero, exp_lt_exp]
        exact div_pos hx ha
      · change a * log (exp (x / a)) = x
        rw [log_exp]
        field_simp [ha.ne']
  have hinj : InjOn (fun t : ℝ ↦ a * log t) (Ioi 1) := by
    intro x hx y hy hxy
    have h := congrArg exp (mul_left_cancel₀ ha.ne' hxy)
    simpa only [exp_log (lt_trans zero_lt_one hx),
      exp_log (lt_trans zero_lt_one hy)] using h
  have hiff :
      IntegrableOn
        (fun x : ℝ ↦ (log x - log a) * exp (-x) / a) (Ioi 0) ↔
      IntegrableOn
        (fun t : ℝ ↦ |a * t⁻¹| •
          ((log (a * log t) - log a) * exp (-(a * log t)) / a))
        (Ioi 1) := by
    rw [← himage]
    apply integrableOn_image_iff_integrableOn_abs_deriv_smul
    · exact measurableSet_Ioi
    · intro t ht
      exact ((hasDerivAt_log (ne_of_gt (lt_trans zero_lt_one ht))).const_mul
        a).hasDerivWithinAt
    · exact hinj
  refine (hiff.mp hg).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hlt : log (a * log t) - log a = log (log t) := by
    rw [log_mul ha.ne' (log_pos ht).ne']
    ring
  have hexp : exp (-(a * log t)) = t * t ^ (-s) := by
    calc
      exp (-(a * log t)) = exp (log t + log t * (-s)) := by
        congr 1
        dsimp [a]
        ring
      _ = t * t ^ (-s) := by
        rw [exp_add, exp_log ht0, rpow_def_of_pos ht0]
  change |a * t⁻¹| •
      ((log (a * log t) - log a) * exp (-(a * log t)) / a) =
    log (log t) * t ^ (-s)
  rw [smul_eq_mul, abs_of_pos (mul_pos ha (inv_pos.mpr ht0)), hlt, hexp]
  field_simp [ha.ne', ht0.ne'] <;> ring
