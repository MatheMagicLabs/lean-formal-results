/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Chebyshev.sum_PrimePow_eq_sum_sum'
Source:      Mathlib @ d0a050ad6, Mathlib/NumberTheory/Chebyshev.lean, line 336
             (added after the model's training data; human proof 30 tactic steps)
Experiment:  P1-astra-long-proofs, arm P, solved after 5 call(s)
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
  have hdecomp : (∑ n ∈ Ioc 0 ⌊x⌋₊ with IsPrimePow n, f n) = ∑ k ∈ Icc 1 N, ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime ∧ p ^ k ≤ ⌊x⌋₊, f (p ^ k) := by
    classical
    symm
    rw [← sum_sigma (Icc 1 N)
      (fun k ↦ {p ∈ Ioc 0 ⌊x⌋₊ | p.Prime ∧ p ^ k ≤ ⌊x⌋₊})
      (fun a : Σ _ : ℕ, ℕ ↦ f (a.2 ^ a.1))]
    refine sum_bij (fun a _ ↦ a.2 ^ a.1) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [mem_sigma, mem_Icc, mem_filter, mem_Ioc] at ha
      simp only [mem_filter, mem_Ioc]
      refine ⟨⟨pow_pos ha.2.1.1 _, ha.2.2.2⟩, ?_⟩
      rw [isPrimePow_nat_iff]
      exact ⟨a.2, a.1, ha.2.2.1, by omega, rfl⟩
    · intro a ha b hb hab
      simp only [mem_sigma, mem_Icc, mem_filter, mem_Ioc] at ha hb
      have hab' : a.2 = b.2 ∧ a.1 = b.1 := by
        grind [Prime.pow_inj']
      rcases a with ⟨k, p⟩
      rcases b with ⟨l, q⟩
      dsimp at hab'
      rcases hab' with ⟨rfl, rfl⟩
      rfl
    · intro n hn
      simp only [mem_filter, mem_Ioc] at hn
      have hprime := hn.2
      rw [isPrimePow_nat_iff] at hprime
      obtain ⟨p, k, hp, hk, rfl⟩ := hprime
      have hpn : p ≤ ⌊x⌋₊ :=
        (le_of_dvd (by omega) (dvd_pow_self p hk.ne')).trans hn.1.2
      have htwo : (2 : ℕ) ^ k ≤ p ^ k := by
        gcongr
        exact hp.two_le
      have hpx : ((p ^ k : ℕ) : ℝ) ≤ x :=
        (Nat.cast_le.mpr hn.1.2).trans (floor_le hx)
      have htwo_real : (2 : ℝ) ^ k ≤ x := by
        exact le_trans (by exact_mod_cast htwo) hpx
      have hlog := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ k) htwo_real
      rw [Real.log_pow] at hlog
      have hkfloor : k ≤ ⌊log x / log 2⌋₊ := by
        apply (le_floor_iff' hk.ne').2
        exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2 hlog
      refine ⟨⟨k, p⟩, ?_, rfl⟩
      simp only [mem_sigma, mem_Icc, mem_filter, mem_Ioc]
      exact ⟨⟨hk, hkfloor.trans hN⟩, ⟨hp.pos, hpn⟩, hp, hn.1.2⟩
    · intro a ha
      rfl
  have hsets : ∀ k ∈ Icc 1 N, {p ∈ Ioc 0 ⌊x⌋₊ | p.Prime ∧ p ^ k ≤ ⌊x⌋₊} = {p ∈ Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ | p.Prime} := by
    intro k hk
    have hkpos : 0 < k := (mem_Icc.mp hk).1
    have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
    have hmul : (k : ℝ) * (1 / (k : ℝ)) = 1 := by
      field_simp
    have hmul' : (1 / (k : ℝ)) * (k : ℝ) = 1 := by
      field_simp
    have hroot (p : ℕ) :
        (p : ℝ) ^ k ≤ x ↔ (p : ℝ) ≤ x ^ ((1 : ℝ) / k) := by
      constructor
      · intro h
        have h' := Real.rpow_le_rpow
          (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ k) h
          (by positivity : (0 : ℝ) ≤ 1 / (k : ℝ))
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p),
          hmul, Real.rpow_one] at h'
        exact h'
      · intro h
        have h' := Real.rpow_le_rpow (Nat.cast_nonneg p) h hkR.le
        rw [← Real.rpow_mul hx, hmul', Real.rpow_one,
          Real.rpow_natCast] at h'
        exact h'
    ext p
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨hp0, hpx⟩, hp, hpow⟩
      refine ⟨⟨hp0, (le_floor_iff (Real.rpow_nonneg hx _)).2 ?_⟩, hp⟩
      apply (hroot p).mp
      have h : ((p ^ k : ℕ) : ℝ) ≤ x :=
        (Nat.cast_le.mpr hpow).trans (floor_le hx)
      exact_mod_cast h
    · rintro ⟨⟨hp0, hpr⟩, hp⟩
      have hpowR : (p : ℝ) ^ k ≤ x :=
        (hroot p).mpr ((le_floor_iff (Real.rpow_nonneg hx _)).mp hpr)
      have hpow : p ^ k ≤ ⌊x⌋₊ := by
        apply (le_floor_iff hx).2
        exact_mod_cast hpowR
      have hpx : p ≤ ⌊x⌋₊ :=
        (le_of_dvd (pow_pos hp0 _) (dvd_pow_self p hkpos.ne')).trans hpow
      exact ⟨⟨hp0, hpx⟩, hp, hpow⟩
  rw [hdecomp]
  exact sum_congr rfl fun k hk ↦ sum_congr (hsets k hk) fun p hp ↦ rfl
