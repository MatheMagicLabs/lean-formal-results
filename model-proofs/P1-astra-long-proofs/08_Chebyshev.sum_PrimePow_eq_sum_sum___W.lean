/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Chebyshev.sum_PrimePow_eq_sum_sum'
Source:      Mathlib @ d0a050ad6, Mathlib/NumberTheory/Chebyshev.lean, line 336
             (added after the model's training data; human proof 30 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 5 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem sum_PrimePow_eq_sum_sum' {R : Type*} [AddCommMonoid R] (f : ℕ → R) {x : ℝ} (hx : 0 ≤ x)
  {N : ℕ} (hN : ⌊log x / log 2⌋₊ ≤ N) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊ with IsPrimePow n, f n
      = ∑ k ∈ Icc 1 N, ∑ p ∈ Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime, f (p ^ k) := by
  have hroot (p k : ℕ) (hk : 0 < k) : (p : ℝ) ≤ x ^ ((1 : ℝ) / k) ↔ (p : ℝ) ^ k ≤ x := by { have hk' : (0 : ℝ) < k := by { exact_mod_cast hk }; constructor; · { intro h; have h' := Real.rpow_le_rpow (Nat.cast_nonneg p) h hk'.le; rw [← Real.rpow_mul hx, one_div_mul_cancel (ne_of_gt hk'), Real.rpow_one, Real.rpow_natCast] at h'; exact h' }; · { intro h; have he : (p : ℝ) = ((p : ℝ) ^ k) ^ ((1 : ℝ) / k) := by { rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]; simp [ne_of_gt hk'] }; exact he.trans_le (Real.rpow_le_rpow (by positivity) h (by positivity)) } }
  symm
  trans ∑ a ∈ (Icc 1 N).sigma (fun k : ℕ ↦ (Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter Nat.Prime), f (a.2 ^ a.1)
  · symm; apply Finset.sum_sigma
  refine sum_bij (fun a _ ↦ a.2 ^ a.1) ?_ ?_ ?_ ?_
  · intro a ha; simp only [mem_sigma, mem_Icc, mem_filter, mem_Ioc] at ha; have hk : 0 < a.1 := by { omega }; have hp : (a.2 : ℝ) ≤ x ^ ((1 : ℝ) / a.1) := (Nat.le_floor_iff (Real.rpow_nonneg hx _)).mp ha.2.1.2; exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨pow_pos ha.2.1.1 _, (Nat.le_floor_iff hx).mpr (by exact_mod_cast (hroot a.2 a.1 hk).mp hp)⟩, by { rw [isPrimePow_nat_iff]; exact ⟨a.2, a.1, ha.2.2, hk, rfl⟩ }⟩
  · intro a ha b hb hab; simp only [mem_sigma, mem_Icc, mem_filter, mem_Ioc] at ha hb; have hp : a.2 = b.2 := by { grind [Prime.pow_inj'] }; have hk : a.1 = b.1 := by { grind [Prime.pow_inj'] }; exact Sigma.ext hk (heq_of_eq hp)
  · intro n hn; simp only [mem_filter, mem_Ioc] at hn; have hn' := hn.2; rw [isPrimePow_nat_iff] at hn'; obtain ⟨p, k, hp, hk, rfl⟩ := hn'; have hpx : (p : ℝ) ^ k ≤ x := by { exact_mod_cast (Nat.le_floor_iff hx).mp hn.1.2 }; have hlog : (k : ℝ) * log (p : ℝ) ≤ log x := by { rw [← Real.log_pow]; exact Real.log_le_log (by exact_mod_cast pow_pos hp.pos k) hpx }; have hp2 : (2 : ℝ) ≤ p := by { exact_mod_cast hp.two_le }; have hlp : log (2 : ℝ) ≤ log (p : ℝ) := Real.log_le_log (by norm_num) hp2; have hl2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num); have hkl : (k : ℝ) ≤ log x / log 2 := (le_div_iff₀ hl2).mpr ((mul_le_mul_of_nonneg_left hlp (Nat.cast_nonneg k)).trans hlog); have hkN : k ≤ N := ((Nat.le_floor_iff' hk.ne').mpr hkl).trans hN; refine ⟨⟨k, p⟩, ?_, rfl⟩; simp only [mem_sigma, mem_Icc, mem_filter, mem_Ioc]; exact ⟨⟨hk, hkN⟩, ⟨⟨hp.pos, (Nat.le_floor_iff (Real.rpow_nonneg hx _)).mpr ((hroot p k hk).mpr hpx)⟩, hp⟩⟩
  · intro a ha; rfl
