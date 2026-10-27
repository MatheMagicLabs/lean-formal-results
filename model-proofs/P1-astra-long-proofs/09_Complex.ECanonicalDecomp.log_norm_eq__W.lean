/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Complex.ECanonicalDecomp.log_norm_eq
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/Complex/CanonicalDecomposition.lean, line 621
             (added after the model's training data; human proof 27 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 3 call(s)
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
  have logprod (a : ℂ → ℂ) (d : ℂ → ℤ) (hd : d.support.Finite)
      (ha : ∀ i, a i ^ d i ≠ 0) :
      Real.log ‖∏ᶠ i, a i ^ d i‖ =
        ∑ᶠ i, (d i : ℝ) * Real.log ‖a i‖ := by
    lift d.support to Finset ℂ using hd with s hs
    have hp : (∏ᶠ i, a i ^ d i) = ∏ i ∈ s, a i ^ d i := by
      apply finprod_eq_prod_of_mulSupport_subset
      simpa [hs] using mulSupport_pow_subset_support a d
    have hsum :
        (∑ᶠ i, (d i : ℝ) * Real.log ‖a i‖) =
          ∑ i ∈ s, (d i : ℝ) * Real.log ‖a i‖ := by
      apply finsum_eq_sum_of_support_subset
      have hsub :
          (fun i ↦ (d i : ℝ) * Real.log ‖a i‖).support ⊆ d.support := by
        intro i hi
        contrapose! hi
        simp_all [Function.mem_support]
      simpa [hs] using hsub
    rw [hp, hsum]
    clear hs hp hsum
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, norm_mul,
        Real.log_mul (norm_ne_zero_iff.mpr (ha i))
          (norm_ne_zero_iff.mpr
            (Finset.prod_ne_zero_iff.mpr (fun j _ ↦ ha j))),
        norm_zpow, Real.log_zpow, ih]
  have hc : ∀ i, canonicalFactor R i w ^ divisor f (ball 0 R) i ≠ 0 := by
    intro i
    by_cases hi : divisor f (ball 0 R) i = 0
    · simp [hi]
    have himem : i ∈ ball 0 R :=
      (divisor f (ball 0 R)).supportWithinDomain hi
    have hwi : w ≠ i := by
      rintro rfl
      exact hi (by
        simp [(D.meromorphicOn.mono_set ball_subset_closedBall).divisor_apply himem,
          h₂w])
    exact zpow_ne_zero _ (canonicalFactor_ne_zero himem h₁w hwi)
  have hs : ∀ i, (w - i) ^ (-(divisor f (sphere 0 R) i)) ≠ 0 := by
    intro i
    by_cases hi : divisor f (sphere 0 R) i = 0
    · simp [hi]
    have himem : i ∈ sphere 0 R :=
      (divisor f (sphere 0 R)).supportWithinDomain hi
    have hwi : w ≠ i := by
      rintro rfl
      exact hi (by
        simp [(D.meromorphicOn.mono_set sphere_subset_closedBall).divisor_apply himem,
          h₂w])
    exact zpow_ne_zero _ (sub_ne_zero.mpr hwi)
  have hfinite : (divisor f (sphere 0 R)).support.Finite :=
    divisor_sphere_support_finite
  have hcLog := logprod (fun i ↦ canonicalFactor R i w)
    (fun i ↦ divisor f (ball 0 R) i)
    D.meromorphicOn.divisor_ball_support_finite hc
  have hsLog := logprod (fun i ↦ w - i)
    (fun i ↦ -(divisor f (sphere 0 R) i))
    (by simpa using hfinite) hs
  have heq := D.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt h₁w h₂w hR
  have hp :
      ((∏ᶠ i, canonicalFactor R i w ^ divisor f (ball 0 R) i) *
        (∏ᶠ i, (w - i) ^ (-divisor f (sphere 0 R)) i)) ≠ 0 := by
    intro hz
    apply D.ne_zero w h₁w
    rw [heq, hz, zero_smul]
  have ht : meromorphicTrailingCoeffAt f w ≠ 0 :=
    (D.meromorphicOn w h₁w).meromorphicTrailingCoeffAt_ne_zero (by simp [h₂w])
  simp only [locallyFinsuppWithin.coe_neg, Pi.neg_apply] at heq hp
  rw [heq, norm_smul,
    Real.log_mul (norm_ne_zero_iff.mpr hp) (norm_ne_zero_iff.mpr ht),
    norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr (mul_ne_zero_iff.mp hp).1)
      (norm_ne_zero_iff.mpr (mul_ne_zero_iff.mp hp).2),
    hcLog, hsLog]
  simp only [Int.cast_neg, neg_mul]
  lift (divisor f (sphere 0 R)).support to Finset ℂ using hfinite with s hsupp
  have hsum (q : ℂ → ℝ)
      (hq : ∀ i, divisor f (sphere 0 R) i = 0 → q i = 0) :
      (∑ᶠ i, q i) = ∑ i ∈ s, q i := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    change q i ≠ 0 at hi
    have hdi : divisor f (sphere 0 R) i ≠ 0 := by
      intro hz
      exact hi (hq i hz)
    simpa [hsupp, Function.mem_support] using hdi
  have hpos := hsum
    (fun i ↦ (divisor f (sphere 0 R) i : ℝ) * Real.log ‖w - i‖)
    (by intro i hi; simp [hi])
  have hneg := hsum
    (fun i ↦ -((divisor f (sphere 0 R) i : ℝ) * Real.log ‖w - i‖))
    (by intro i hi; simp [hi])
  rw [hneg, hpos, Finset.sum_neg_distrib]
  simp only [sub_eq_add_neg]
