/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     map_add_eq_sum_add_integral_iteratedFDeriv
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/Calculus/TaylorIntegral.lean, line 69
             (added after the model's training data; human proof 54 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 8 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem map_add_eq_sum_add_integral_iteratedFDeriv (hf : ∀ (t : ℝ) (_ht : t ∈ Set.Icc 0 1),
    ContDiffAt ℝ (n + 1) f (x + t • y)) :
    f (x + y) = ∑ k ∈ Finset.range (n + 1), (k ! : ℝ)⁻¹ • (iteratedFDeriv ℝ k f x (fun _ ↦ y)) +
    (n ! : ℝ)⁻¹ • ∫ t in 0..1, (1 - t)^n • iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ ↦ y) := by
  let D : ℕ → ℝ → F := fun k t => iteratedFDeriv ℝ k f (x + t • y) (fun _ ↦ y)
  have hc (m k : ℕ) (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ (m + 1) f (x + t • y)) (hk : k ≤ m + 1) : ContinuousOn (D k) (Set.Icc 0 1) := by
  {
  intro t ht
  have h' : ContinuousAt (iteratedFDeriv ℝ k f) (x + t • y) := by
  {
  apply (h t ht).continuousAt_iteratedFDeriv
  exact_mod_cast hk
  }
  have hp : ContinuousAt (fun s : ℝ ↦ x + s • y) t := (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
  have hh : ContinuousAt (fun s : ℝ ↦ iteratedFDeriv ℝ k f (x + s • y)) t := h'.comp (f := fun s : ℝ ↦ x + s • y) hp
  have hid : DifferentiableAt ℝ (fun g : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) F ↦ g) (iteratedFDeriv ℝ k f (x + t • y)) := differentiableAt_id
  have hev : DifferentiableAt ℝ (fun g : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) F ↦ g (fun _ ↦ y)) (iteratedFDeriv ℝ k f (x + t • y)) := hid.continuousMultilinear_apply_const _
  exact (hev.continuousAt.comp (f := fun s : ℝ ↦ iteratedFDeriv ℝ k f (x + s • y)) hh).continuousWithinAt
  }
  have hd (m k : ℕ) (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ (m + 1) f (x + t • y)) (hk : k < m + 1) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : HasDerivAt (D k) (D (k + 1) t) t := by
  {
  have h' : ContDiffAt ℝ (k + 1) f (x + t • y) := by
  {
  apply (h t ht).of_le
  exact_mod_cast (show k + 1 ≤ m + 1 from hk)
  }
  have hg : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) (x + t • y) := by
  {
  apply h'.differentiableAt_iteratedFDeriv
  exact_mod_cast Nat.lt_succ_self k
  }
  have hp : DifferentiableAt ℝ (fun s : ℝ ↦ x + s • y) t := ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const y)).differentiableAt
  have heval : DifferentiableAt ℝ (fun z : E ↦ iteratedFDeriv ℝ k f z (fun _ ↦ y)) (x + t • y) := hg.continuousMultilinear_apply_const _
  have hh : DifferentiableAt ℝ (D k) t := by
  {
  change DifferentiableAt ℝ ((fun z : E ↦ iteratedFDeriv ℝ k f z (fun _ ↦ y)) ∘ (fun s : ℝ ↦ x + s • y)) t
  exact heval.comp t hp
  }
  simpa only [D, h'.deriv_fderiv_add_smul] using hh.hasDerivAt
  }
  have hi (m k p : ℕ) (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ (m + 1) f (x + t • y)) (hk : k ≤ m + 1) : IntervalIntegrable (fun t : ℝ ↦ (1 - t)^p • D k t) MeasureTheory.volume 0 1 := by
  {
  have hs : Continuous (fun t : ℝ ↦ (1 - t)^p) := (continuous_const.sub continuous_id).pow p
  have hv : ContinuousOn (fun t : ℝ ↦ (1 - t)^p • D k t) (Set.Icc 0 1) := hs.continuousOn.smul (hc m k h hk)
  apply ContinuousOn.intervalIntegrable
  simpa only [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hv
  }
  revert hf
  induction n with
  | zero => {
  intro hf
  have h_int : IntervalIntegrable (D 1) MeasureTheory.volume 0 1 := by
  {
  simpa using hi 0 1 0 hf (le_refl 1)
  }
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht ↦ hd 0 0 hf (Nat.zero_lt_succ 0) t (by simpa only [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht)) h_int
  simp [D] at he ⊢
  rw [he]
  abel
  }
  | succ n ih => {
  intro hf
  have hlow : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ (n + 1) f (x + t • y) := by
  {
  intro t ht
  apply (hf t ht).of_le
  exact_mod_cast Nat.le_succ (n + 1)
  }
  have hA := hi (n + 1) (n + 1) n hf (Nat.le_succ (n + 1))
  have hB := hi (n + 1) (n + 2) (n + 1) hf (le_refl (n + 2))
  have hp (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : HasDerivAt (fun s : ℝ ↦ (1 - s)^(n + 1) • D (n + 1) s) ((1 - t)^(n + 1) • D (n + 2) t - (n + 1 : ℝ) • ((1 - t)^n • D (n + 1) t)) t := by
  {
  have hs : HasDerivAt (fun s : ℝ ↦ (1 - s)^(n + 1)) (-((n + 1 : ℝ) * (1 - t)^n)) t := by
  {
  have hs₀ := ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).pow (n + 1)
  change HasDerivAt (fun s : ℝ ↦ (1 - s)^(n + 1)) ((↑(n + 1) : ℝ) * (1 - t)^(n + 1 - 1) * (0 - 1)) t at hs₀
  simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, zero_sub, mul_neg, mul_one] using hs₀
  }
  have hv := hd (n + 1) (n + 1) hf (Nat.lt_succ_self (n + 1)) t ht
  change HasDerivAt (D (n + 1)) (D (n + 2) t) t at hv
  have hp₀ := hs.smul hv
  change HasDerivAt (fun s : ℝ ↦ (1 - s)^(n + 1) • D (n + 1) s) ((1 - t)^(n + 1) • D (n + 2) t + (-((n + 1 : ℝ) * (1 - t)^n)) • D (n + 1) t) t at hp₀
  simpa only [neg_smul, mul_smul, sub_eq_add_neg] using hp₀
  }
  have hC : IntervalIntegrable (fun t : ℝ ↦ (n + 1 : ℝ) • ((1 - t)^n • D (n + 1) t)) MeasureTheory.volume 0 1 := hA.smul (n + 1 : ℝ)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht ↦ hp t (by simpa only [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht)) (hB.sub hC)
  rw [intervalIntegral.integral_sub hB hC, intervalIntegral.integral_smul] at he
  simp only [sub_self, sub_zero, zero_pow (Nat.succ_ne_zero n), zero_smul, one_pow, one_smul, zero_sub] at he
  have hrec : (∫ t in (0 : ℝ)..1, (1 - t)^(n + 1) • D (n + 2) t) = (n + 1 : ℝ) • (∫ t in (0 : ℝ)..1, (1 - t)^n • D (n + 1) t) - D (n + 1) 0 := by
  {
  rw [sub_eq_iff_eq_add] at he
  rw [he]
  abel
  }
  have hfac : ((n + 1)! : ℝ)⁻¹ * (n + 1 : ℝ) = (n ! : ℝ)⁻¹ := by
  {
  have hn : (n + 1 : ℝ) ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one)
  simp [Nat.factorial_succ, Nat.cast_mul, mul_inv_rev, mul_assoc, hn]
  }
  rw [Finset.sum_range_succ, ih hlow]
  change (∑ k ∈ Finset.range (n + 1), (k ! : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ ↦ y)) + (n ! : ℝ)⁻¹ • (∫ t in (0 : ℝ)..1, (1 - t)^n • D (n + 1) t) = ((∑ k ∈ Finset.range (n + 1), (k ! : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ ↦ y)) + ((n + 1)! : ℝ)⁻¹ • iteratedFDeriv ℝ (n + 1) f x (fun _ ↦ y)) + ((n + 1)! : ℝ)⁻¹ • (∫ t in (0 : ℝ)..1, (1 - t)^(n + 1) • D (n + 2) t)
  rw [hrec, smul_sub, smul_smul, hfac]
  simp only [D, zero_smul, add_zero]
  abel
  }
