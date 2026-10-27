/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     DirichletCharacter.eulerProduct_log_eq_LSeries
Source:      Mathlib @ d0a050ad6, Mathlib/NumberTheory/EulerProduct/DirichletLSeries.lean, line 221
             (added after the model's training data; human proof 29 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 2 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem DirichletCharacter.eulerProduct_log_eq_LSeries (hs : 1 < s.re) :
    ∑' p : Primes, -log (1 - χ p * p ^ (-s)) = LSeries (fun n ↦ χ n * Λ n / Real.log n) s := by
  let f := dirichletSummandHom χ (ne_zero_of_one_lt_re hs)
  let g : ℕ → ℂ := fun n ↦ χ n * Λ n / Real.log n
  have hg : LSeriesSummable g s := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
    intro n hn
    by_cases hn₁ : n = 1
    · simp [g, hn₁]
    have hlog : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    dsimp [g]
    rw [norm_div, norm_mul, Complex.norm_of_nonneg vonMangoldt_nonneg,
      Complex.norm_of_nonneg hlog.le]
    apply (div_le_one hlog).mpr
    exact (mul_le_of_le_one_left vonMangoldt_nonneg (χ.norm_le_one n)).trans
      vonMangoldt_le_log
  have ht (n : ℕ) :
      term g s n = f n * (Λ n : ℂ) / (Real.log n : ℂ) := by
    rw [term_of_ne_zero' (ne_zero_of_one_lt_re hs)]
    simp only [g, f, dirichletSummandHom, MonoidWithZeroHom.coe_mk,
      ZeroHom.coe_mk, cpow_neg]
    ring
  have hsupport :
      Function.support (term g s) ⊆ {n | IsPrimePow n} := by
    intro n hn
    by_contra h
    have hz : Λ n = 0 := vonMangoldt_eq_zero_iff.mpr h
    exact hn (by simp [ht, hz])
  change _ = ∑' n : ℕ, term g s n
  rw [tsum_eq_tsum_primes_of_support_subset_prime_powers hg hsupport]
  apply tsum_congr
  intro p
  have hp : ‖f p‖ < 1 :=
    (summable_dirichletSummand χ hs).of_norm.norm_lt_one
      (f := f.toMonoidHom) p.prop.one_lt
  change -log (1 - f p) = _
  rw [← (hasSum_taylorSeries_neg_log' hp).tsum_eq]
  apply tsum_congr
  intro k
  rw [ht, map_pow, vonMangoldt_apply_pow (Nat.succ_ne_zero k),
    vonMangoldt_apply_prime p.prop]
  have hlog : (Real.log (p : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos
      (show (1 : ℝ) < (p : ℕ) by exact_mod_cast p.prop.one_lt)).ne'
  simp only [Nat.cast_pow, Real.log_pow, Complex.ofReal_mul,
    Complex.ofReal_natCast, Nat.cast_add, Nat.cast_one]
  field_simp
  push_cast
  rfl
