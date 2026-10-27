/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.deriv_Gamma_one_eq_integral_log_log
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Gamma/Deriv.lean, line 191
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 2 (round 0 = first attempt)
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

theorem deriv_Gamma_one_eq_integral_log_log {s : ℝ} (hs : 1 < s) :
    deriv Gamma 1 = (s - 1) * (∫ t in Ioi 1, log (log t) * t ^ (-s)) + log (s - 1) := by
  have hc0 : 0 < s - 1 := sub_pos.mpr hs
  have hc : s - 1 ≠ 0 := hc0.ne'
  have himg : (fun u : ℝ => Real.exp (u / (s - 1))) '' Ioi 0 = Ioi 1 := by
    ext t
    simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact Real.one_lt_exp_iff.mpr (div_pos hu hc0)
    · intro ht
      refine ⟨(s - 1) * Real.log t, mul_pos hc0 (Real.log_pos ht), ?_⟩
      rw [mul_div_cancel_left₀ _ hc, Real.exp_log (by linarith)]
  have hderiv : ∀ x ∈ Ioi (0:ℝ), HasDerivWithinAt (fun u : ℝ => Real.exp (u / (s - 1)))
      (Real.exp (x / (s - 1)) * (1 / (s - 1))) (Ioi 0) x :=
    fun x _ => ((hasDerivAt_id x).div_const (s - 1)).exp.hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => Real.exp (u / (s - 1))) (Ioi 0) := by
    intro x _ y _ h
    have h2 : x / (s - 1) = y / (s - 1) := Real.exp_injective h
    rwa [div_left_inj' hc] at h2
  have hpt : EqOn (fun u => |Real.exp (u / (s - 1)) * (1 / (s - 1))| •
      (Real.log (Real.log (Real.exp (u / (s - 1)))) * Real.exp (u / (s - 1)) ^ (-s)))
      (fun u => 1 / (s - 1) * (Real.log (u / (s - 1)) * Real.exp (-u))) (Ioi 0) := by
    intro u hu
    have he : Real.exp (u / (s - 1)) * Real.exp (u / (s - 1) * -s) = Real.exp (-u) := by
      rw [← Real.exp_add]
      congr 1
      have : u / (s - 1) * (s - 1) = u := div_mul_cancel₀ u hc
      linear_combination -this
    simp only [smul_eq_mul, Real.log_exp]
    rw [abs_of_pos (mul_pos (Real.exp_pos _) (one_div_pos.mpr hc0)), ← Real.exp_mul, ← he]
    ring
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun t => Real.log (Real.log t) * t ^ (-s))
  beta_reduce at key
  rw [himg, setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul] at key
  have hInt := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun t => Real.log (Real.log t) * t ^ (-s))).mp
    (by rw [himg]; exact Real.integrableOn_log_log_mul_rpow hs)
  have hA : IntegrableOn (fun u => Real.log (u / (s - 1)) * Real.exp (-u)) (Ioi 0) := by
    have h1 := Integrable.const_mul (IntegrableOn.congr_fun hInt hpt measurableSet_Ioi) (s - 1)
    refine IntegrableOn.congr_fun h1 (fun u _ => ?_) measurableSet_Ioi
    simp only [← mul_assoc, mul_one_div_cancel hc, one_mul]
  have hexp : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Ioi 0) :=
    IntegrableOn.congr_fun (exp_neg_integrableOn_Ioi 0 one_pos) (fun x _ => by simp)
      measurableSet_Ioi
  have hsplit : ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t)
      = ∫ u in Ioi (0:ℝ), (Real.log (u / (s - 1)) * Real.exp (-u)
          + Real.log (s - 1) * Real.exp (-u)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    rw [Real.log_div (mem_Ioi.mp hu).ne' hc]
    ring
  rw [Real.deriv_Gamma_one_eq_integral_log, key, hsplit,
    integral_add hA (Integrable.const_mul hexp (Real.log (s - 1))),
    integral_const_mul, integral_exp_neg_Ioi_zero, ← mul_assoc, mul_one_div_cancel hc]
  ring
