/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MvPowerSeries.IsRestricted.add
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/MvPowerSeries/Restricted.lean, line 110
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma add {c : σ → ℝ} {f g : MvPowerSeries σ R} (hf : IsRestricted c f)
    (hg : IsRestricted c g) : IsRestricted c (f + g) := by
  rw [← isRestricted_abs_iff] at hf hg ⊢
  unfold IsRestricted at hf hg ⊢
  refine tendsto_const_nhds.squeeze (zero_add (0:ℝ) ▸ hf.add hg) (fun t ↦ ?_) fun t ↦ ?_
  · dsimp [Finsupp.prod]; positivity
  · dsimp only
    rw [map_add, ← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by dsimp [Finsupp.prod]; positivity)
