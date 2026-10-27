/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Complex.ECanonicalDecomp.log_norm_eq
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/Complex/CanonicalDecomposition.lean, line 621
             (added after the model's training data; human proof 27 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 1 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma ECanonicalDecomp.log_norm_eq
    {f h : ℂ → E} (D : ECanonicalDecomp f h R) (h₁w : w ∈ closedBall 0 R)
    (h₂w : meromorphicOrderAt f w = 0)
    (hR : 0 < R) :
    Real.log ‖h w‖ = ((∑ᶠ i, (divisor f (ball 0 R) i) * Real.log ‖canonicalFactor R i w‖)
          - (∑ᶠ i, (divisor f (sphere 0 R) i) * Real.log ‖w - i‖))
          + Real.log ‖meromorphicTrailingCoeffAt f w‖ := by
  classical
  have log_prod_aux (a : ℂ → ℂ) (n : ℂ → ℤ)
      (hn : n.support.Finite) (ha : ∀ i, a i ^ n i ≠ 0) :
      Real.log ‖∏ᶠ i, a i ^ n i‖ = ∑ᶠ i, (n i : ℝ) * Real.log ‖a i‖ := by
    let s := hn.toFinset
    have hs : ∀ i, i ∉ s → n i = 0 := by
      intro i hi
      simpa [s, Function.mem_support] using hi
    have hp : (fun i ↦ a i ^ n i).mulSupport ⊆ (s : Set ℂ) := by
      intro i hi
      by_contra hi'
      simp [Function.mem_mulSupport, hs i hi'] at hi
    have hsum : (fun i ↦ (n i : ℝ) * Real.log ‖a i‖).support ⊆
        (s : Set ℂ) := by
      intro i hi
      by_contra hi'
      simp [Function.mem_support, hs i hi'] at hi
    rw [finprod_eq_prod_of_mulSupport_subset _ hp,
      finsum_eq_sum_of_support_subset _ hsum, norm_prod,
      Real.log_prod (fun i _ ↦ norm_ne_zero_iff.mpr (ha i))]
    simp only [norm_zpow, Real.log_zpow]
  have hb : ∀ i, canonicalFactor R i w ^ divisor f (ball 0 R) i ≠ 0 := by
    intro i
    by_cases hi : divisor f (ball 0 R) i = 0
    · simp [hi]
    have hiB : i ∈ ball 0 R := (divisor f (ball 0 R)).supportWithinDomain hi
    have hwi : w ≠ i := by
      rintro rfl
      apply hi
      simp [(D.meromorphicOn.mono_set ball_subset_closedBall).divisor_apply hiB, h₂w]
    exact zpow_ne_zero _ (canonicalFactor_ne_zero hiB h₁w hwi)
  have hs : ∀ i, (w - i) ^ (-divisor f (sphere 0 R)) i ≠ 0 := by
    intro i
    by_cases hi : divisor f (sphere 0 R) i = 0
    · simp [hi]
    have hiS : i ∈ sphere 0 R := (divisor f (sphere 0 R)).supportWithinDomain hi
    have hwi : w ≠ i := by
      rintro rfl
      apply hi
      simp [(D.meromorphicOn.mono_set sphere_subset_closedBall).divisor_apply hiS, h₂w]
    exact zpow_ne_zero _ (sub_ne_zero.mpr hwi)
  have ht : meromorphicTrailingCoeffAt f w ≠ 0 :=
    (D.meromorphicOn w h₁w).meromorphicTrailingCoeffAt_ne_zero (by simp [h₂w])
  have hsfin : (fun i ↦ (-divisor f (sphere 0 R)) i).support.Finite := by
    simpa using (divisor_sphere_support_finite (f := f) (R := R) (c := (0 : ℂ)))
  rw [D.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt h₁w h₂w hR,
    norm_smul, Real.log_mul
      (norm_ne_zero_iff.mpr (mul_ne_zero (finprod_ne_zero hb) (finprod_ne_zero hs)))
      (norm_ne_zero_iff.mpr ht),
    norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (finprod_ne_zero hb))
      (norm_ne_zero_iff.mpr (finprod_ne_zero hs)),
    log_prod_aux _ _ D.meromorphicOn.divisor_ball_support_finite hb,
    log_prod_aux _ _ hsfin hs]
  simp only [locallyFinsuppWithin.coe_neg, Pi.neg_apply, Int.cast_neg, neg_mul,
    finsum_neg_distrib, sub_eq_add_neg]
