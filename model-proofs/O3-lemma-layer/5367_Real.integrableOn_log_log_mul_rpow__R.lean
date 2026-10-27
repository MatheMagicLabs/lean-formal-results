/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.integrableOn_log_log_mul_rpow
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Gamma/Deriv.lean, line 170
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 3 (round 0 = first attempt)
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
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Ioi (0:ℝ))
    (f := Real.exp) (f' := Real.exp) measurableSet_Ioi
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun t ↦ Real.log (Real.log t) * t ^ (-s))
  have himg : Real.exp '' Ioi 0 = Ioi 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : (0:ℝ) < x := hx
      show 1 < Real.exp x
      simpa using hx'
    · intro hy
      have hy' : (1:ℝ) < y := hy
      exact ⟨Real.log y, Real.log_pos hy', Real.exp_log (by linarith)⟩
  rw [himg] at h
  rw [h]
  have hmain : IntegrableOn (fun x : ℝ => Real.log x * Real.exp (-(s-1)*x)) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    refine IntegrableOn.union ?_ ?_
    · have h1 : IntegrableOn Real.log (Ioc (0:ℝ) 1) := by
        first
          | exact (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1)).1
          | exact (intervalIntegrable_log' (a := 0) (b := 1)).1
          | exact (_root_.intervalIntegrable_log' (a := 0) (b := 1)).1
      exact h1.mul_continuousOn_of_subset
        (by fun_prop : Continuous fun x : ℝ => Real.exp (-(s-1)*x)).continuousOn
        measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self
    · have h2 : IntegrableOn (fun x : ℝ => x ^ (1:ℝ) * Real.exp (-(s-1) * x ^ (1:ℝ)))
          (Ioi 0) :=
        integrableOn_rpow_mul_exp_neg_mul_rpow (by first | linarith | norm_num)
          (by first | linarith | norm_num) (by first | linarith | norm_num)
      simp only [Real.rpow_one] at h2
      refine Integrable.mono' (h2.mono_set (Ioi_subset_Ioi zero_le_one)) ?_ ?_
      · exact (Real.measurable_log.mul
          (Real.measurable_exp.comp (measurable_const.mul measurable_id))).aestronglyMeasurable
      · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
        have hx' : (1:ℝ) < x := hx
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          abs_of_nonneg (Real.log_nonneg hx'.le)]
        exact mul_le_mul_of_nonneg_right
          ((Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith))
          (Real.exp_pos _).le
  refine hmain.congr_fun (fun x _ => ?_) measurableSet_Ioi
  show Real.log x * Real.exp (-(s-1)*x)
    = |Real.exp x| • (Real.log (Real.log (Real.exp x)) * Real.exp x ^ (-s))
  rw [abs_of_pos (Real.exp_pos x), smul_eq_mul, Real.log_exp,
    Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]
  rw [show -(s-1)*x = x + x * -s by ring, Real.exp_add]
  ring
