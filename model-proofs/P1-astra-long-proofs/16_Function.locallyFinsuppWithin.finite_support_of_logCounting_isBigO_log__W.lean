/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Function.locallyFinsuppWithin.finite_support_of_logCounting_isBigO_log
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Asymptotic.lean, line 116
             (added after the model's training data; human proof 28 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 2 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma finite_support_of_logCounting_isBigO_log [ProperSpace E]
    {D : locallyFinsupp E ℤ} (h : 0 ≤ D) (hO : logCounting D =O[atTop] Real.log) :
    D.support.Finite := by
  classical
  by_contra hfin
  obtain ⟨c, hc⟩ := isBigO_iff.1 hO
  obtain ⟨n, hn⟩ := exists_nat_gt (c + 1)
  have hinf : Set.Infinite D.support := hfin
  obtain ⟨s, hs, hcard⟩ := hinf.exists_subset_card_eq n
  let F : locallyFinsupp E ℤ := ∑ e ∈ s, single e 1
  have hFD : F ≤ D := by {
  intro x
  by_cases hx : x ∈ s
  · {
  have hxD : D x ≠ 0 := hs hx
  have hDx : 0 ≤ D x := h x
  have hDx' : (1 : ℤ) ≤ D x := by omega
  simpa [F, single_apply, hx] using hDx'
  }
  · {
  have hDx : 0 ≤ D x := h x
  simpa [F, single_apply, hx] using hDx
  }
  }
  let C : ℝ := ∑ e ∈ s, log ‖e‖
  have hC : (fun _ : ℝ ↦ C) =o[atTop] Real.log :=
  isLittleO_const_log_atTop
  have hCe := isLittleO_iff.1 hC (show (0 : ℝ) < 1 by norm_num)
  have hf : ∀ᶠ r : ℝ in atTop, False := by {
  filter_upwards [hc, hCe, eventually_gt_atTop (1 : ℝ),
  eventually_ge_atTop (∑ e ∈ s, ‖e‖)] with r hr hCr hr1 hrs
  have hlog : 0 < log r := log_pos hr1
  have hcalc : logCounting F r = (s.card : ℝ) * log r - C := by {
  calc
  logCounting F r = ∑ e ∈ s, (log r - log ‖e‖) := by {
  simp only [F, map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro e he
  have her : ‖e‖ ≤ r :=
  (Finset.single_le_sum (fun i _ ↦ norm_nonneg i) he).trans hrs
  rw [logCounting_single_eq_log_sub_const her]
  simp
  }
  _ = (s.card : ℝ) * log r - C := by {
  simp [C, Finset.sum_sub_distrib]
  }
  }
  have hle := logCounting_le hFD hr1.le
  have hbound : logCounting D r ≤ c * log r := by {
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlog] at hr
  exact (le_abs_self _).trans hr
  }
  have hCbound : C ≤ log r := by {
  have habs : |C| ≤ log r := by {
  simpa only [Real.norm_eq_abs, abs_of_pos hlog, one_mul] using hCr
  }
  exact (le_abs_self C).trans habs
  }
  rw [hcalc, hcard] at hle
  nlinarith
  }
  obtain ⟨r, hr⟩ := hf.exists
  exact hr
