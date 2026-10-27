/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Complex.ECanonicalDecomp.log_norm_eq
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/Complex/CanonicalDecomposition.lean, line 621
             (added after the model's training data; human proof 27 tactic steps)
Experiment:  P1-astra-long-proofs, arm P, solved after 4 call(s)
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
  let A : ℂ := ∏ᶠ i, (canonicalFactor R i w) ^ (divisor f (ball 0 R) i)
  let B : ℂ := ∏ᶠ i, (w - i) ^ (-divisor f (sphere 0 R)) i
  let T : E := meromorphicTrailingCoeffAt f w
  have hlogA : Real.log ‖A‖ = ∑ᶠ i, (divisor f (ball 0 R) i : ℝ) * Real.log ‖canonicalFactor R i w‖ := by
    classical
    lift (divisor f (ball 0 R)).support to Finset ℂ using
      D.meromorphicOn.divisor_ball_support_finite with t ht
    have hne (i : ℂ) :
        canonicalFactor R i w ^ (divisor f (ball 0 R) i) ≠ 0 := by
      by_cases hi : divisor f (ball 0 R) i = 0
      · simp [hi]
      have hiB : i ∈ ball 0 R :=
        (divisor f (ball 0 R)).supportWithinDomain hi
      have hwi : w ≠ i := by
        rintro rfl
        exact hi (by
          simp [(D.meromorphicOn.mono_set ball_subset_closedBall).divisor_apply hiB,
            h₂w])
      exact zpow_ne_zero _ (canonicalFactor_ne_zero hiB h₁w hwi)
    have hs :
        Function.support (fun i ↦
          (divisor f (ball 0 R) i : ℝ) * Real.log ‖canonicalFactor R i w‖) ⊆
          (t : Set ℂ) := by
      intro i hi
      by_contra hn
      have hz : divisor f (ball 0 R) i = 0 := by
        simpa [ht] using hn
      simpa [hz] using hi
    change Real.log ‖∏ᶠ i, canonicalFactor R i w ^ (divisor f (ball 0 R) i)‖ = _
    rw [finprod_eq_prod_of_mulSupport_subset (s := t) _ (by
      simpa [ht] using
        mulSupport_pow_subset_support (fun i ↦ canonicalFactor R i w)
          (fun i ↦ divisor f (ball 0 R) i))]
    rw [finsum_eq_sum_of_support_subset _ hs]
    rw [norm_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro i hi
      simp only [norm_zpow, Real.log_zpow]
    · intro i hi
      exact norm_ne_zero_iff.mpr (hne i)
  have hlogB : Real.log ‖B‖ = -(∑ᶠ i, (divisor f (sphere 0 R) i : ℝ) * Real.log ‖w - i‖) := by
    classical
    lift (divisor f (sphere 0 R)).support to Finset ℂ using
      divisor_sphere_support_finite with t ht
    have hne (i : ℂ) :
        (w - i) ^ (-divisor f (sphere 0 R)) i ≠ 0 := by
      by_cases hi : divisor f (sphere 0 R) i = 0
      · simp [hi]
      have hiS : i ∈ sphere 0 R :=
        (divisor f (sphere 0 R)).supportWithinDomain hi
      have hwi : w ≠ i := by
        rintro rfl
        exact hi (by
          simp [(D.meromorphicOn.mono_set sphere_subset_closedBall).divisor_apply hiS,
            h₂w])
      exact zpow_ne_zero _ (sub_ne_zero.mpr hwi)
    have hs :
        Function.support (fun i ↦
          (divisor f (sphere 0 R) i : ℝ) * Real.log ‖w - i‖) ⊆
          (t : Set ℂ) := by
      intro i hi
      by_contra hn
      have hz : divisor f (sphere 0 R) i = 0 := by
        simpa [ht] using hn
      simpa [hz] using hi
    change Real.log ‖∏ᶠ i, (w - i) ^ (-divisor f (sphere 0 R)) i‖ = _
    rw [finprod_eq_prod_of_mulSupport_subset (s := t) _ (by
      simpa [ht] using
        mulSupport_pow_subset_support (fun i ↦ w - i)
          (fun i ↦ (-divisor f (sphere 0 R)) i))]
    rw [finsum_eq_sum_of_support_subset _ hs]
    rw [norm_prod, Real.log_prod]
    · rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simp [norm_zpow, Real.log_zpow]
    · intro i hi
      exact norm_ne_zero_iff.mpr (hne i)
  have hlogmul : Real.log ‖(A * B) • T‖ = Real.log ‖A‖ + Real.log ‖B‖ + Real.log ‖T‖ := by
    have hdecomp : h w = (A * B) • T :=
      D.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt h₁w h₂w hR
    have hn : (A * B) • T ≠ 0 := by
      rw [← hdecomp]
      exact D.ne_zero w h₁w
    have hA : A ≠ 0 := by
      intro hz
      simp [hz] at hn
    have hB : B ≠ 0 := by
      intro hz
      simp [hz] at hn
    have hT : T ≠ 0 := by
      intro hz
      simp [hz] at hn
    rw [norm_smul, norm_mul,
      Real.log_mul
        (mul_ne_zero (norm_ne_zero_iff.mpr hA) (norm_ne_zero_iff.mpr hB))
        (norm_ne_zero_iff.mpr hT),
      Real.log_mul (norm_ne_zero_iff.mpr hA) (norm_ne_zero_iff.mpr hB)]
  have hdecomp : h w = (A * B) • T :=
    D.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt h₁w h₂w hR
  rw [hdecomp, hlogmul, hlogA, hlogB]
  rfl
