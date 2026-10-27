/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Seminorm.egauge_ball_le_of_one_lt_norm
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Convex/EGauge.lean, line 338
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma egauge_ball_le_of_one_lt_norm (hc : 1 < ‖c‖) (h₀ : r ≠ 0 ∨ p x ≠ 0) :
    egauge 𝕜 (p.ball 0 r) x ≤ ‖c‖ₑ * (p x).toNNReal / r := by
  have hc0 : c ≠ 0 := norm_pos_iff.1 (one_pos.trans hc)
  by_cases hr : r = 0
  · subst hr
    have hpx : p x ≠ 0 := h₀.resolve_left (by simp)
    have hpos : 0 < p x := lt_of_le_of_ne (apply_nonneg p x) (Ne.symm hpx)
    rw [ENNReal.coe_zero, ENNReal.div_zero (mul_ne_zero (enorm_ne_zero.2 hc0)
      (ENNReal.coe_ne_zero.2 (Real.toNNReal_pos.2 hpos).ne'))]
    exact le_top
  by_cases hpx : p x = 0
  · have h0 : (p x).toNNReal = 0 := by simp [hpx]
    rw [h0, ENNReal.coe_zero, mul_zero, ENNReal.zero_div]
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    have hc1 : ‖c‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hc
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (NNReal.coe_pos.2 hε) hc1
    have hmem : c ^ n • x ∈ p.ball 0 r := by
      rw [p.mem_ball_zero, map_smul_eq_mul, hpx, mul_zero]
      exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 hr)
    refine (egauge_le_of_smul_mem_of_ne hmem (pow_ne_zero n hc0)).trans ?_
    rw [zero_add, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    rw [inv_pow] at hn
    simpa using hn.le
  have hr' : (0 : ℝ) < r := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hr)
  obtain ⟨d, hd0, hlt, -, hinv⟩ := p.rescale_to_shell hc hr' hpx
  refine (egauge_le_of_smul_mem_of_ne (p.mem_ball_zero.2 hlt) hd0).trans ?_
  rw [enorm_eq_nnnorm, ← ENNReal.coe_mul, ← ENNReal.coe_div hr, ENNReal.coe_le_coe,
    ← NNReal.coe_le_coe]
  simp only [NNReal.coe_inv, coe_nnnorm, NNReal.coe_div, NNReal.coe_mul,
    Real.coe_toNNReal _ (apply_nonneg p x)]
  exact hinv.trans_eq (by ring)
