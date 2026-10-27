/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Chebyshev.sum_PrimePow_eq_sum_sum'
Source:      Mathlib @ d0a050ad6, Mathlib/NumberTheory/Chebyshev.lean, line 336
             (added after the model's training data; human proof 30 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 4 call(s)
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
  classical
  have hroot (p k : ℕ) (hk : 0 < k) : p ≤ ⌊x ^ ((1 : ℝ) / k)⌋₊ ↔ p ^ k ≤ ⌊x⌋₊ := by {
  rw [Nat.le_floor_iff (Real.rpow_nonneg hx _), one_div, Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg p) hx (by exact_mod_cast hk), Real.rpow_natCast, ← Nat.cast_pow, ← Nat.le_floor_iff hx]
  }
  have hbound (p k : ℕ) (hp : p.Prime) (hk : 0 < k) (hpk : p ^ k ≤ ⌊x⌋₊) : k ≤ N := by {
  have hpx : (p : ℝ) ^ k ≤ x := by exact_mod_cast (Nat.le_floor_iff hx).mp hpk
  have htwo : (2 : ℝ) ^ k ≤ x := by {
  calc
  (2 : ℝ) ^ k ≤ (p : ℝ) ^ k := by gcongr; exact_mod_cast hp.two_le
  _ ≤ x := hpx
  }
  have hl : (k : ℝ) ≤ log x / log 2 := (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr (Real.le_log_of_pow_le (by norm_num : (0 : ℝ) < 2) htwo)
  exact ((Nat.le_floor_iff' hk.ne').mpr hl).trans hN
  }
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij (fun a _ ↦ a.2 ^ a.1) ?_ ?_ ?_ ?_
  · {
  intro a ha
  rcases Finset.mem_sigma.mp ha with ⟨hk, hp⟩
  rcases Finset.mem_Icc.mp hk with ⟨hk, hkN⟩
  rcases Finset.mem_filter.mp hp with ⟨hp, hprime⟩
  rcases Finset.mem_Ioc.mp hp with ⟨hp0, hpx⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨pow_pos hp0 _, (hroot _ _ hk).mp hpx⟩, (isPrimePow_nat_iff _).mpr ⟨a.2, a.1, hprime, hk, rfl⟩⟩
  }
  · {
  intro a ha b hb hab
  rcases a with ⟨k, p⟩
  rcases b with ⟨l, q⟩
  simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Finset.mem_Ioc] at ha hb
  have hk : k ≠ 0 := by omega
  have hl : l ≠ 0 := by omega
  obtain ⟨rfl, rfl⟩ := ha.2.2.pow_inj' hb.2.2 hk hl hab
  rfl
  }
  · {
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨hn, hprime⟩
  rcases Finset.mem_Ioc.mp hn with ⟨hn0, hnx⟩
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hprime
  refine ⟨⟨k, p⟩, ?_, rfl⟩
  exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hk, hbound p k hp hk hnx⟩, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp.pos, (hroot p k hk).mpr hnx⟩, hp⟩⟩
  }
  · { intro a ha; rfl }
