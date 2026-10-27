/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Function.locallyFinsuppWithin.finite_support_of_logCounting_isBigO_log
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Asymptotic.lean, line 116
             (added after the model's training data; human proof 28 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 1 call(s)
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
  obtain ⟨C, hC⟩ := isBigO_iff.1 hO
  obtain ⟨n, hn⟩ := exists_nat_gt (C + 1)
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hfin n
  have hle : (∑ e ∈ s, single e (1 : ℤ)) ≤ D := by
  { intro e
    have he0 : 0 ≤ D e := h e
    by_cases he : e ∈ s
    · have hne : D e ≠ 0 := hs he
      have he1 : (1 : ℤ) ≤ D e := by omega
      simpa only [coe_sum, Finset.sum_apply, single_apply, Finset.sum_ite_eq,
        if_pos he] using he1
    · simpa only [coe_sum, Finset.sum_apply, single_apply, Finset.sum_ite_eq,
        if_neg he] using he0 }
  have hR : ∀ᶠ r : ℝ in atTop, ∀ e ∈ s, ‖e‖ ≤ r :=
    (eventually_all_finset s).2 fun e _ ↦ eventually_ge_atTop ‖e‖
  have hL : ∀ᶠ r : ℝ in atTop, (∑ e ∈ s, log ‖e‖) < log r :=
    tendsto_log_atTop.eventually (eventually_gt_atTop _)
  obtain ⟨r, hr, hCr, hRr, hLr⟩ :=
    (eventually_gt_atTop 1 |>.and (hC.and (hR.and hL))).exists
  have hlog : 0 < log r := log_pos hr
  have hupper : logCounting D r ≤ C * log r := by
  { have hnonneg := logCounting_nonneg h hr.le
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg,
      abs_of_pos hlog] using hCr }
  have hlower : (n : ℝ) * log r - (∑ e ∈ s, log ‖e‖) ≤ logCounting D r := by
  { calc
      (n : ℝ) * log r - (∑ e ∈ s, log ‖e‖) =
          ∑ e ∈ s, (log r - log ‖e‖) := by
        rw [Finset.sum_sub_distrib]
        simp [hcard]
      _ = logCounting (∑ e ∈ s, single e (1 : ℤ)) r := by
        rw [map_sum]
        simp only [Finset.sum_apply]
        apply Finset.sum_congr rfl
        intro e he
        simp [logCounting_single_eq_log_sub_const (hRr e he)]
      _ ≤ logCounting D r := logCounting_le hle hr.le }
  have hmul := mul_lt_mul_of_pos_right hn hlog
  nlinarith
