/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Submultiplicative.eventually_rpow_lt_of_rpow_lt
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Subadditive.lean, line 59
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem eventually_rpow_lt_of_rpow_lt (hbdd : ∀ k, 0 ≤ u k) {L : ℝ} {n : ℕ} (hn : n ≠ 0)
    (hL : u n ^ (n : ℝ)⁻¹ < L) : ∀ᶠ p in atTop, u p ^ (p : ℝ)⁻¹ < L := by
  refine .atTop_of_arithmetic hn fun r _ => ?_
  have hL0 : 0 < L := lt_of_le_of_lt (Real.rpow_nonneg (hbdd n) _) hL
  have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  by_cases hr : u r = 0
  · filter_upwards [eventually_gt_atTop 0] with k hk
    have hp : n * k + r ≠ 0 := by
      have := Nat.mul_pos (Nat.pos_of_ne_zero hn) hk; omega
    have h1 := h.apply_mul_add_le k n r (hbdd n)
    rw [hr, mul_zero, mul_comm k n] at h1
    have h2 : u (n * k + r) = 0 := le_antisymm h1 (hbdd _)
    show u (n * k + r) ^ ((n * k + r : ℕ) : ℝ)⁻¹ < L
    rw [h2, Real.zero_rpow (inv_ne_zero (Nat.cast_ne_zero.mpr hp))]
    exact hL0
  · have hg : Tendsto (fun x : ℝ => ((n:ℝ) * x + r)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _
        (Tendsto.const_mul_atTop hnpos tendsto_id))
    have hE : Tendsto (fun x : ℝ => x * ((n:ℝ) * x + r)⁻¹) atTop (𝓝 (n : ℝ)⁻¹) := by
      have : Tendsto (fun x : ℝ => (n : ℝ)⁻¹ - r / n * ((n:ℝ) * x + r)⁻¹) atTop
          (𝓝 ((n : ℝ)⁻¹ - r / n * 0)) := tendsto_const_nhds.sub (tendsto_const_nhds.mul hg)
      rw [mul_zero, sub_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      have hx' : (n : ℝ) * x + r ≠ 0 := by
        have := mul_pos hnpos hx
        have : (0:ℝ) ≤ r := Nat.cast_nonneg r
        exact (show (0:ℝ) < n * x + r by linarith).ne'
      have hn' : (n:ℝ) ≠ 0 := hnpos.ne'
      field_simp
      try ring
    have hF : Tendsto (fun x : ℝ => u n ^ (x * ((n:ℝ) * x + r)⁻¹) * u r ^ (((n:ℝ) * x + r)⁻¹))
        atTop (𝓝 (u n ^ (n : ℝ)⁻¹ * u r ^ (0:ℝ))) :=
      (tendsto_const_nhds.rpow hE (Or.inr (inv_pos.mpr hnpos))).mul
        (tendsto_const_nhds.rpow hg (Or.inl hr))
    rw [Real.rpow_zero, mul_one] at hF
    filter_upwards [(hF.comp tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds hL),
      eventually_gt_atTop 0] with k hk hk0
    have hk' : u n ^ ((k:ℝ) * ((n:ℝ) * k + r)⁻¹) * u r ^ (((n:ℝ) * k + r)⁻¹) < L := hk
    have h1 := h.apply_mul_add_le k n r (hbdd n)
    rw [mul_comm k n] at h1
    show u (n * k + r) ^ ((n * k + r : ℕ) : ℝ)⁻¹ < L
    refine lt_of_le_of_lt ?_ hk'
    push_cast
    calc u (n * k + r) ^ ((n:ℝ) * k + r)⁻¹ ≤ (u n ^ k * u r) ^ ((n:ℝ) * k + r)⁻¹ :=
          Real.rpow_le_rpow (hbdd _) h1 (inv_nonneg.mpr (by positivity))
      _ = _ := by
          rw [Real.mul_rpow (pow_nonneg (hbdd n) k) (hbdd r), ← Real.rpow_natCast,
            ← Real.rpow_mul (hbdd n)]
