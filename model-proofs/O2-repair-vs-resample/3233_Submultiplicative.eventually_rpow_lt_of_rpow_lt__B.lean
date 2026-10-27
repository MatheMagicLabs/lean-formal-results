/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Submultiplicative.eventually_rpow_lt_of_rpow_lt
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Subadditive.lean, line 59
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem eventually_rpow_lt_of_rpow_lt (hbdd : ∀ k, 0 ≤ u k) {L : ℝ} {n : ℕ} (hn : n ≠ 0)
    (hL : u n ^ (n : ℝ)⁻¹ < L) : ∀ᶠ p in atTop, u p ^ (p : ℝ)⁻¹ < L := by
  have hn' : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  refine Filter.Eventually.atTop_of_arithmetic hn fun r _ => ?_
  set C : ℝ := max (u r) 1 with hC
  have hC1 : 1 ≤ C := le_max_right _ _
  have hC0 : 0 < C := by linarith
  have E1 : Tendsto (fun x : ℝ => x * (x * n + r)⁻¹) atTop (𝓝 (n:ℝ)⁻¹) := by
    have A : Tendsto (fun x : ℝ => ((n:ℝ) + r / x)⁻¹) atTop (𝓝 ((n:ℝ) + 0)⁻¹) :=
      ((tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)).inv₀
        (by rw [add_zero]; exact hn'.ne'))
    rw [add_zero] at A
    refine A.congr' ((eventually_gt_atTop 0).mono fun x hx => ?_)
    rw [show (n:ℝ) + r / x = (x * n + r) / x by
      rw [add_div, mul_div_cancel_left₀ _ hx.ne'], inv_div, div_eq_mul_inv]
  have E2 : Tendsto (fun x : ℝ => (x * n + r)⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ _ (tendsto_id.atTop_mul_const hn'))
  have F : Tendsto (fun x : ℝ => u n ^ (x * (x * n + r)⁻¹) * C ^ ((x * n + r)⁻¹)) atTop
      (𝓝 (u n ^ (n:ℝ)⁻¹ * C ^ (0:ℝ))) :=
    ((tendsto_const_nhds.rpow E1 (Or.inr (inv_pos.2 hn'))).mul
      (tendsto_const_nhds.rpow E2 (Or.inl hC0.ne')))
  rw [Real.rpow_zero, mul_one] at F
  refine ((F.comp tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds hL)).mono
    fun k hk' => ?_
  refine lt_of_le_of_lt ?_ hk'
  simp only [Function.comp]
  have hm : ((n * k + r : ℕ) : ℝ) = (k:ℝ) * n + r := by push_cast; ring
  rw [hm]
  have key : u (n * k + r) ≤ u n ^ k * C := by
    rw [mul_comm n k]
    exact (h.apply_mul_add_le k n r (hbdd n)).trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (pow_nonneg (hbdd n) k))
  refine (Real.rpow_le_rpow (hbdd _) key (by positivity)).trans (le_of_eq ?_)
  rw [Real.mul_rpow (pow_nonneg (hbdd n) k) hC0.le, ← Real.rpow_natCast,
    ← Real.rpow_mul (hbdd n)]
