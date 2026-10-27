/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Submultiplicative.eventually_rpow_lt_of_rpow_lt
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Subadditive.lean, line 59
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem eventually_rpow_lt_of_rpow_lt (hbdd : ∀ k, 0 ≤ u k) {L : ℝ} {n : ℕ} (hn : n ≠ 0)
    (hL : u n ^ (n : ℝ)⁻¹ < L) : ∀ᶠ p in atTop, u p ^ (p : ℝ)⁻¹ < L := by
  have hL0 : 0 < L := lt_of_le_of_lt (Real.rpow_nonneg (hbdd n) _) hL
  obtain ⟨M, hM1, hM2⟩ := exists_between (max_lt hL hL0)
  have hM0 : 0 < M := lt_of_le_of_lt (le_max_right _ _) hM1
  have hMn : u n ≤ M ^ n := by
    have h1 : u n ^ ((n:ℝ)⁻¹) < M := lt_of_le_of_lt (le_max_left _ _) hM1
    have := pow_lt_pow_left₀ h1 (Real.rpow_nonneg (hbdd n) _) hn
    rw [Real.rpow_inv_natCast_pow (hbdd n) hn] at this
    exact this.le
  refine .atTop_of_arithmetic hn fun r _ => ?_
  obtain ⟨D, hD⟩ : ∃ D, D = (u r + 1) / M ^ r := ⟨_, rfl⟩
  have hD0 : 0 < D := by
    rw [hD]
    have := hbdd r
    positivity
  have hT : Tendsto (fun p : ℕ => M * D ^ ((p:ℝ)⁻¹)) atTop (𝓝 (M * D ^ (0:ℝ))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.rpow
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop) (Or.inl hD0.ne'))
  rw [Real.rpow_zero, mul_one] at hT
  have hev := hT.eventually (gt_mem_nhds hM2)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  filter_upwards [eventually_ge_atTop (N + 1)] with k hk
  show u (n*k+r) ^ ((n*k+r : ℕ) : ℝ)⁻¹ < L
  have hkn : k ≤ n * k := Nat.le_mul_of_pos_left k (Nat.pos_of_ne_zero hn)
  have hp : n*k+r ≠ 0 := by omega
  have e : M ^ (n*k+r) * D = (M ^ n) ^ k * (u r + 1) := by
    have hMr : M ^ r ≠ 0 := pow_ne_zero r hM0.ne'
    rw [hD, pow_add, ← pow_mul]
    first | (field_simp; done) | (field_simp; ring)
  have hbound : u (n*k+r) ≤ M ^ (n*k+r) * D := by
    rw [e, mul_comm n k]
    refine le_trans (h.apply_mul_add_le k n r (hbdd n)) ?_
    have := hbdd r
    exact mul_le_mul (pow_le_pow_left₀ (hbdd n) hMn k) (by linarith) (hbdd r) (by positivity)
  calc u (n*k+r) ^ (((n*k+r:ℕ)):ℝ)⁻¹
      ≤ (M ^ (n*k+r) * D) ^ (((n*k+r:ℕ)):ℝ)⁻¹ :=
        Real.rpow_le_rpow (hbdd _) hbound (by positivity)
    _ = M * D ^ (((n*k+r:ℕ)):ℝ)⁻¹ := by
        rw [Real.mul_rpow (by positivity) hD0.le, Real.pow_rpow_inv_natCast hM0.le hp]
    _ < L := hN _ (by omega)
