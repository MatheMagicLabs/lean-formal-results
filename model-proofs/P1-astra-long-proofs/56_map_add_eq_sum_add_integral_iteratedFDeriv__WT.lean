/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     map_add_eq_sum_add_integral_iteratedFDeriv
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/Calculus/TaylorIntegral.lean, line 69
             (added after the model's training data; human proof 54 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 6 call(s)
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
  let D : ℕ → ℝ → F := fun k t ↦ iteratedFDeriv ℝ k f (x + t • y) (fun _ ↦ y)
  have hc (m k : ℕ) (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ (m + 1) f (x + t • y)) (hk : k ≤ m + 1) : ContinuousOn (D k) (Set.uIcc 0 1) := by
  {
  intro t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa using ht
  have h₁ := (h t ht').continuousAt_iteratedFDeriv (k := k) (by exact_mod_cast hk)
  have h₂ : ContinuousAt (fun s : ℝ ↦ x + s • y) t := by fun_prop
  have h₃ := h₁.comp (f := fun s : ℝ ↦ x + s • y) h₂
  exact (h₃.eval_const (fun _ ↦ y)).continuousWithinAt
  }
  have hd (m k : ℕ) (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ (m + 1) f (x + t • y)) (hk : k + 1 ≤ m + 1) : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (D k) (D (k + 1) t) t := by
  {
  intro t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa using ht
  have h₁ : ContDiffAt ℝ (k + 1) f (x + t • y) := (h t ht').of_le (by exact_mod_cast hk)
  have h₂ := h₁.differentiableAt_iteratedFDeriv (m := k) (by exact_mod_cast Nat.lt_succ_self k)
  have hp : DifferentiableAt ℝ (fun s : ℝ ↦ x + s • y) t := by fun_prop
  have h₃ : DifferentiableAt ℝ (D k) t := (h₂.continuousMultilinear_apply_const (fun _ ↦ y)).comp t (f := fun s : ℝ ↦ x + s • y) hp
  have he : deriv (D k) t = D (k + 1) t := h₁.deriv_fderiv_add_smul
  rw [← he]
  exact h₃.hasDerivAt
  }
  have main : ∀ m : ℕ, (∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ (m + 1) f (x + t • y)) → D 0 1 = ∑ k ∈ Finset.range (m + 1), (k ! : ℝ)⁻¹ • D k 0 + (m ! : ℝ)⁻¹ • ∫ t in 0..1, (1 - t)^m • D (m + 1) t := by
  {
  intro m
  induction m with
  | zero =>
  {
  intro h
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (hd 0 0 h (by omega)) ((hc 0 1 h (by omega)).intervalIntegrable)
  simp only [Nat.zero_add, Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero]
  rw [hi]
  abel
  }
  | succ m ih =>
  {
  intro h
  have hlow : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ (m + 1) f (x + t • y) := by
  {
  intro t ht
  exact (h t ht).of_le (by exact_mod_cast Nat.le_succ (m + 1))
  }
  have hu : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ ↦ (1 - s)^(m + 1)) (-((m + 1 : ℕ) : ℝ) * (1 - t)^m) t := by
  {
  intro t ht
  have hh : HasDerivAt (fun s : ℝ ↦ (1 - s)^(m + 1)) (((m + 1 : ℕ) : ℝ) * (1 - t)^m * (-1)) t := by
  {
  simpa using ((hasDerivAt_id t).const_sub (1 : ℝ)).fun_pow (m + 1)
  }
  have he : -((m + 1 : ℕ) : ℝ) * (1 - t)^m = ((m + 1 : ℕ) : ℝ) * (1 - t)^m * (-1) := by ring
  rw [he]
  exact hh
  }
  have hui : IntervalIntegrable (fun t : ℝ ↦ -((m + 1 : ℕ) : ℝ) * (1 - t)^m) MeasureTheory.volume 0 1 := (show Continuous (fun t : ℝ ↦ -((m + 1 : ℕ) : ℝ) * (1 - t)^m) from by fun_prop).intervalIntegrable 0 1
  have hj := intervalIntegral.integral_smul_deriv_eq_deriv_smul hu (hd (m + 1) (m + 1) h (by omega)) hui ((hc (m + 1) (m + 2) h (by omega)).intervalIntegrable)
  simp only [sub_self, sub_zero, zero_pow (by omega : m + 1 ≠ 0), one_pow, zero_smul, one_smul, zero_sub] at hj
  simp_rw [mul_smul, neg_smul, intervalIntegral.integral_neg, intervalIntegral.integral_smul, sub_neg_eq_add] at hj
  have hfac : ((m + 1)! : ℝ)⁻¹ * ((m + 1 : ℕ) : ℝ) = (m ! : ℝ)⁻¹ := by
  {
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
  }
  change D 0 1 = ∑ k ∈ Finset.range ((m + 1) + 1), (k ! : ℝ)⁻¹ • D k 0 + ((m + 1)! : ℝ)⁻¹ • ∫ t in 0..1, (1 - t)^(m + 1) • D ((m + 1) + 1) t
  rw [Finset.sum_range_succ, hj, smul_add, smul_neg, smul_smul, hfac, ih hlow]
  abel
  }
  }
  simpa [D, iteratedFDeriv_zero_apply] using main n hf
