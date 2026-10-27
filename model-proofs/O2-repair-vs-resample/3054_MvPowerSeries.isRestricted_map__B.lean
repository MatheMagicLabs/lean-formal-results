/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MvPowerSeries.isRestricted_map
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/MvPowerSeries/Restricted.lean, line 98
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma isRestricted_map {S : Type*} [NormedRing S] (c : σ → ℝ) (π : R → S) {C : ℝ}
    (hCπ : ∀ x, ‖π x‖ ≤ C * ‖x‖) {f : MvPowerSeries σ R} (hf : IsRestricted c f) :
    IsRestricted c (fun t ↦ π (coeff t f) : MvPowerSeries σ S) := by
  dsimp only [IsRestricted] at hf ⊢
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (hf.norm.const_mul |C|)
  simp only [norm_zero, mul_zero] at h
  refine squeeze_zero (fun t ↦ norm_nonneg _) (fun t ↦ ?_) h
  have h1 : ‖π (coeff t f)‖ ≤ |C| * ‖coeff t f‖ :=
    (hCπ _).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))
  change ‖‖π (coeff t f)‖ * t.prod (c · ^ ·)‖ ≤ |C| * ‖‖coeff t f‖ * t.prod (c · ^ ·)‖
  rw [norm_mul, norm_mul, norm_norm, norm_norm, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
