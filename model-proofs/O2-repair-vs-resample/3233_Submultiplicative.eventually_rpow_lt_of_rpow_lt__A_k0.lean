/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Submultiplicative.eventually_rpow_lt_of_rpow_lt
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Subadditive.lean, line 59
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem eventually_rpow_lt_of_rpow_lt (hbdd : ∀ k, 0 ≤ u k) {L : ℝ} {n : ℕ} (hn : n ≠ 0)
    (hL : u n ^ (n : ℝ)⁻¹ < L) : ∀ᶠ p in atTop, u p ^ (p : ℝ)⁻¹ < L := by
  have hL0 : 0 < L := lt_of_le_of_lt (Real.rpow_nonneg (hbdd n) _) hL
  have hab : u n < L ^ n := by
    have := pow_lt_pow_left₀ hL (Real.rpow_nonneg (hbdd n) _) hn
    rwa [Real.rpow_inv_natCast_pow (hbdd n) hn] at this
  have hb : 0 < L ^ n := pow_pos hL0 n
  suffices H : ∀ᶠ p in atTop, u p < L ^ p by
    filter_upwards [H, eventually_ne_atTop 0] with p hp hp0
    calc u p ^ (p : ℝ)⁻¹ < (L ^ p) ^ (p : ℝ)⁻¹ :=
          Real.rpow_lt_rpow (hbdd p) hp
            (inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hp0)))
      _ = L := Real.pow_rpow_inv_natCast hL0.le hp0
  refine Filter.Eventually.atTop_of_arithmetic hn fun r _ => ?_
  have hlim : Tendsto (fun k : ℕ => (u n / L ^ n) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg (hbdd n) hb.le) ((div_lt_one hb).mpr hab)
  have hr1 : 0 < u r + 1 := by linarith [hbdd r]
  have hpos : 0 < L ^ r / (u r + 1) := div_pos (pow_pos hL0 r) hr1
  filter_upwards [hlim.eventually (gt_mem_nhds hpos)] with k hk
  have h1 := h.apply_mul_add_le k n r (hbdd n)
  rw [div_pow, div_lt_div_iff₀ (pow_pos hb k) hr1] at hk
  calc u (n * k + r) = u (k * n + r) := by rw [mul_comm]
    _ ≤ u n ^ k * u r := h1
    _ ≤ u n ^ k * (u r + 1) := by
        have := pow_nonneg (hbdd n) k
        nlinarith
    _ < L ^ r * (L ^ n) ^ k := hk
    _ = L ^ (n * k + r) := by rw [pow_add, pow_mul]; ring
