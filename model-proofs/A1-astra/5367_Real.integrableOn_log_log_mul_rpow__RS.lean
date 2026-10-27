/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.integrableOn_log_log_mul_rpow
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Gamma/Deriv.lean, line 170
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 0 (round 0 = first attempt)
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

theorem integrableOn_log_log_mul_rpow {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t ↦ log (log t) * t ^ (-s)) (Ioi 1) := by
  have hbound (x : ℝ) (hx : 0 < x) :
      ‖log x‖ ≤ 2 * (x ^ (-1 / 2 : ℝ) + x ^ (1 / 2 : ℝ)) := by
    have hn := log_le_sub_one_of_pos (rpow_pos_of_pos hx (-1 / 2 : ℝ))
    have hp := log_le_sub_one_of_pos (rpow_pos_of_pos hx (1 / 2 : ℝ))
    rw [log_rpow hx] at hn hp
    rw [Real.norm_eq_abs, abs_le]
    constructor <;>
      nlinarith [rpow_pos_of_pos hx (-1 / 2 : ℝ),
        rpow_pos_of_pos hx (1 / 2 : ℝ)]
  have hn : IntegrableOn
      (fun x : ℝ ↦ x ^ (-1 / 2 : ℝ) * exp (-(s - 1) * x)) (Ioi 0) := by
    simpa only [rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (-1 / 2 : ℝ)) (p := 1) (b := s - 1)
        (by norm_num) (by norm_num) (by linarith))
  have hp : IntegrableOn
      (fun x : ℝ ↦ x ^ (1 / 2 : ℝ) * exp (-(s - 1) * x)) (Ioi 0) := by
    simpa only [rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (1 / 2 : ℝ)) (p := 1) (b := s - 1)
        (by norm_num) (by norm_num) (by linarith))
  have hg : IntegrableOn
      (fun x : ℝ ↦ log x * exp (-(s - 1) * x)) (Ioi 0) := by
    refine ((hn.add hp).const_mul 2).mono' ?_ ?_
    · exact (by
        fun_prop : Measurable
          (fun x : ℝ ↦ log x * exp (-(s - 1) * x))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [norm_mul, Real.norm_of_nonneg (le_of_lt (exp_pos _))]
      calc
        ‖log x‖ * exp (-(s - 1) * x) ≤
            (2 * (x ^ (-1 / 2 : ℝ) + x ^ (1 / 2 : ℝ))) *
              exp (-(s - 1) * x) :=
          mul_le_mul_of_nonneg_right (hbound x hx) (le_of_lt (exp_pos _))
        _ = 2 * (x ^ (-1 / 2 : ℝ) * exp (-(s - 1) * x) +
            x ^ (1 / 2 : ℝ) * exp (-(s - 1) * x)) := by ring
  have ht := (integrableOn_comp_log_Ioi
    (fun x : ℝ ↦ log x * exp (-(s - 1) * x))
    (by norm_num : (0 : ℝ) < 1)).2 (by simpa only [log_one] using hg)
  apply Integrable.congr ht
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  change x⁻¹ * (log (log x) * exp (-(s - 1) * log x)) =
    log (log x) * x ^ (-s)
  rw [rpow_def_of_pos hx0]
  calc
    x⁻¹ * (log (log x) * exp (-(s - 1) * log x)) =
        log (log x) * (exp (-log x) * exp (-(s - 1) * log x)) := by
      rw [exp_neg, exp_log hx0]
      ring
    _ = log (log x) * exp (log x * (-s)) := by
      rw [← exp_add]
      congr 2
      ring
