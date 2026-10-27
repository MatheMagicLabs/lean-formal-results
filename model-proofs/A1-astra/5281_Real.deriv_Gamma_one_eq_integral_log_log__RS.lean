/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.deriv_Gamma_one_eq_integral_log_log
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Gamma/Deriv.lean, line 191
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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

theorem deriv_Gamma_one_eq_integral_log_log {s : ℝ} (hs : 1 < s) :
    deriv Gamma 1 = (s - 1) * (∫ t in Ioi 1, log (log t) * t ^ (-s)) + log (s - 1) := by
  have ha : 0 < s - 1 := sub_pos.mpr hs
  have hpow : (∫ t : ℝ in Ioi 1, t ^ (-s)) = 1 / (s - 1) := by
    rw [integral_Ioi_rpow_of_lt (by linarith : -s < -1) zero_lt_one,
      one_rpow]
    apply (div_eq_div_iff (by linarith : -s + 1 ≠ 0) ha.ne').2
    ring
  have hi : IntegrableOn (fun t : ℝ ↦ t ^ (-s)) (Ioi 1) := by
    by_contra h
    have hz : (∫ t : ℝ in Ioi 1, t ^ (-s)) = 0 := integral_undef h
    rw [hpow] at hz
    exact (div_ne_zero one_ne_zero ha.ne') hz
  have hd : ∀ x ∈ Ioi (1 : ℝ),
      HasDerivWithinAt (fun t ↦ (s - 1) * log t)
        ((s - 1) / x) (Ioi 1) x := by
    intro x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    simpa only [div_eq_mul_inv] using
      ((hasDerivAt_log hx0.ne').const_mul (s - 1)).hasDerivWithinAt
  have hinj : InjOn (fun t : ℝ ↦ (s - 1) * log t) (Ioi 1) := by
    intro x hx y hy hxy
    have hlog : log x = log y := mul_left_cancel₀ ha.ne' hxy
    have he := congrArg exp hlog
    simpa only [exp_log (lt_trans zero_lt_one hx),
      exp_log (lt_trans zero_lt_one hy)] using he
  have himage : (fun t : ℝ ↦ (s - 1) * log t) '' Ioi 1 = Ioi 0 := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact mul_pos ha (log_pos hx)
    · intro y hy
      refine ⟨exp (y / (s - 1)), ?_, ?_⟩
      · exact one_lt_exp_iff.mpr (div_pos hy ha)
      · change (s - 1) * log (exp (y / (s - 1))) = y
        rw [log_exp]
        field_simp
  rw [deriv_Gamma_one_eq_integral_log]
  calc
    (∫ t in Ioi (0 : ℝ), log t * exp (-t)) =
        ∫ t in Ioi (1 : ℝ), |(s - 1) / t| •
          (log ((s - 1) * log t) * exp (-((s - 1) * log t))) := by
      simpa only [himage] using
        (integral_image_eq_integral_abs_deriv_smul
          measurableSet_Ioi hd hinj (fun t : ℝ ↦ log t * exp (-t)))
    _ = ∫ t in Ioi (1 : ℝ),
        ((s - 1) * (log (log t) * t ^ (-s)) +
          ((s - 1) * log (s - 1)) * t ^ (-s)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      have hp : exp (-((s - 1) * log t)) / t = t ^ (-s) := by
        calc
          exp (-((s - 1) * log t)) / t =
              t ^ (1 - s) / t ^ (1 : ℝ) := by
            rw [rpow_one, rpow_def_of_pos ht0]
            congr 2
            ring
          _ = t ^ ((1 - s) - 1) := (rpow_sub ht0 _ _).symm
          _ = t ^ (-s) := by congr 1 <;> ring
      change |(s - 1) / t| *
        (log ((s - 1) * log t) * exp (-((s - 1) * log t))) = _
      rw [abs_of_pos (div_pos ha ht0),
        log_mul ha.ne' (log_pos ht).ne']
      calc
        _ = (s - 1) * (log (log t) *
              (exp (-((s - 1) * log t)) / t)) +
            ((s - 1) * log (s - 1)) *
              (exp (-((s - 1) * log t)) / t) := by ring
        _ = _ := by rw [hp]
    _ = (s - 1) * (∫ t in Ioi 1, log (log t) * t ^ (-s)) +
        log (s - 1) := by
      rw [integral_add
        ((integrableOn_log_log_mul_rpow hs).const_mul (s - 1))
        (hi.const_mul ((s - 1) * log (s - 1))),
        integral_const_mul, integral_const_mul, hpow]
      field_simp
      <;> ring
