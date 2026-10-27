/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.integrableOn_log_log_mul_rpow
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Gamma/Deriv.lean, line 170
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem integrableOn_log_log_mul_rpow {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t ↦ log (log t) * t ^ (-s)) (Ioi 1) := by
  have hu : Ioi (1:ℝ) = Ioc 1 2 ∪ Ioi 2 := (Ioc_union_Ioi_eq_Ioi (by norm_num)).symm
  have hmeas : AEStronglyMeasurable (fun t : ℝ ↦ log (log t) * t ^ (-s)) volume :=
    ((Real.measurable_log.comp Real.measurable_log).mul
      (measurable_id.pow_const (-s))).aestronglyMeasurable
  rw [hu]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntervalIntegrable (fun t : ℝ ↦ log (t - 1)) volume 1 2 := by
      open intervalIntegral in
      have := (intervalIntegrable_log' (a := 0) (b := 1)).comp_sub_right 1
      norm_num at this
      exact this
    have h2' : IntervalIntegrable (fun t : ℝ ↦ ‖log (t - 1)‖ + log 2) volume 1 2 :=
      h1.norm.add intervalIntegrable_const
    have h2 : IntegrableOn (fun t : ℝ ↦ ‖log (t - 1)‖ + log 2) (Ioc 1 2) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp h2'
    refine Integrable.mono' h2 hmeas.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    show ‖log (log t) * t ^ (-s)‖ ≤ ‖log (t - 1)‖ + log 2
    obtain ⟨ht1, ht2⟩ := ht
    have ht0 : t ≠ 0 := by intro h; linarith
    have hlog : 0 < log t := Real.log_pos ht1
    have hlog1 : log t < 1 := by
      have := Real.log_lt_sub_one_of_pos (by linarith : (0:ℝ) < t) (by intro h; linarith)
      linarith
    have hll : log (log t) < 0 := Real.log_neg hlog hlog1
    have hge : (t - 1) / 2 ≤ log t := by
      have h3 := Real.one_sub_inv_le_log_of_pos (by linarith : (0:ℝ) < t)
      have e : 1 - t⁻¹ = (t - 1) / t := by field_simp
      have h4 : (t - 1) / 2 ≤ (t - 1) / t :=
        div_le_div_of_nonneg_left (by linarith) (by linarith) ht2
      linarith
    have h5 : log ((t - 1) / 2) ≤ log (log t) := Real.log_le_log (by linarith) hge
    rw [Real.log_div (by intro h; linarith) (by norm_num)] at h5
    have hp0 : 0 ≤ t ^ (-s) := Real.rpow_nonneg (by linarith) _
    have hp1 : t ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1.le (by linarith)
    simp only [Real.norm_eq_abs]
    rw [abs_mul, abs_of_neg hll, abs_of_nonneg hp0]
    have h6 := neg_le_abs (log (t - 1))
    have h7 := mul_le_mul_of_nonneg_left hp1 (neg_nonneg.mpr hll.le)
    linarith
  · obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (s - 1) / 2 := ⟨_, rfl⟩
    have hε0 : 0 < ε := by rw [hε]; linarith
    have i1 : IntegrableOn (fun t : ℝ ↦ t ^ (ε + -s)) (Ioi 2) :=
      integrableOn_Ioi_rpow_of_lt (by rw [hε]; linarith) two_pos
    have i2 : IntegrableOn (fun t : ℝ ↦ t ^ (-s)) (Ioi 2) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) two_pos
    have i3 : IntegrableOn (fun t : ℝ ↦ t ^ (ε + -s) / ε + 2 * t ^ (-s)) (Ioi 2) :=
      (Integrable.div_const i1 ε).add (Integrable.const_mul i2 2)
    refine Integrable.mono' i3 hmeas.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    show ‖log (log t) * t ^ (-s)‖ ≤ t ^ (ε + -s) / ε + 2 * t ^ (-s)
    have ht2 : (2:ℝ) < t := ht
    have ht0 : 0 < t := by linarith
    have hl2 : (1/2:ℝ) < log t := by
      have h3 := Real.one_sub_inv_le_log_of_pos ht0
      have h4 : 1 / t < 1 / 2 := one_div_lt_one_div_of_lt two_pos ht2
      have h5 : t⁻¹ = 1 / t := (one_div t).symm
      linarith
    have hlpos : 0 < log t := by linarith
    have hup : log (log t) ≤ log t := by
      have := Real.log_le_sub_one_of_pos hlpos; linarith
    have hlow : -log (log t) ≤ 2 := by
      have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hlpos)
      rw [Real.log_inv] at h
      have : (log t)⁻¹ < 2 := by
        rw [inv_lt_comm₀ hlpos two_pos]
        have : (2:ℝ)⁻¹ = 1/2 := by norm_num
        linarith
      linarith
    have hrp : log t ≤ t ^ ε / ε := Real.log_le_rpow_div ht0.le hε0
    have hp0 : 0 ≤ t ^ (-s) := Real.rpow_nonneg ht0.le _
    have hq : 0 ≤ t ^ ε / ε := div_nonneg (Real.rpow_nonneg ht0.le ε) hε0.le
    have habs : |log (log t)| ≤ t ^ ε / ε + 2 := by
      rw [abs_le]; constructor <;> linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp0, Real.rpow_add ht0]
    calc |log (log t)| * t ^ (-s) ≤ (t ^ ε / ε + 2) * t ^ (-s) :=
          mul_le_mul_of_nonneg_right habs hp0
      _ = t ^ ε * t ^ (-s) / ε + 2 * t ^ (-s) := by ring
