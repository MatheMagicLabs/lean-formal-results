/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.integrableOn_log_log_mul_rpow
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Gamma/Deriv.lean, line 170
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  have key : IntegrableOn (fun u : ℝ => log u * exp ((1 - s) * u)) (Ioi 0) := by
    have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1/2) (b := s-1)
      (by norm_num) one_pos (by linarith)
    have h2 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -(1/2)) (b := s-1)
      (by norm_num) one_pos (by linarith)
    refine Integrable.mono' ((h1.add h2).const_mul 2) ?_ ?_
    · exact (measurable_log.mul (measurable_const.mul measurable_id).exp).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu : (0:ℝ) < u := hu
      have hb : |log u| ≤ 2 * (u^(1/2:ℝ) + u^(-(1/2):ℝ)) := by
        have ha0 := rpow_nonneg hu.le (1/2:ℝ)
        have hb0 := rpow_nonneg hu.le (-(1/2):ℝ)
        have h1 := Real.log_le_rpow_div hu.le (by norm_num : (0:ℝ) < 1/2)
        have h2 := Real.log_le_rpow_div (inv_nonneg.mpr hu.le) (by norm_num : (0:ℝ) < 1/2)
        rw [Real.log_inv, Real.inv_rpow hu.le, ← Real.rpow_neg hu.le] at h2
        have e1 : u^(1/2:ℝ)/(1/2) = 2*u^(1/2:ℝ) := by ring
        have e2 : u^(-(1/2):ℝ)/(1/2) = 2*u^(-(1/2):ℝ) := by ring
        rw [e1] at h1
        rw [e2] at h2
        rw [abs_le]; constructor <;> linarith
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      simp only [Pi.add_apply, rpow_one]
      have e : -(s-1)*u = (1-s)*u := by ring
      rw [e]
      have hE := exp_pos ((1-s)*u)
      have := mul_le_mul_of_nonneg_right hb hE.le
      exact this.trans (le_of_eq (by ring))
  have h3 := (integrableOn_comp_log_Ioi (fun u => log u * exp ((1-s)*u)) one_pos).mpr
    (by rwa [log_one])
  refine h3.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : 0 < t := lt_trans one_pos ht
  simp only [smul_eq_mul]
  rw [mul_comm (1-s), ← rpow_def_of_pos ht0, rpow_sub ht0, rpow_one, rpow_neg ht0.le]
  have : 0 < t ^ s := rpow_pos_of_pos ht0 s
  field_simp
