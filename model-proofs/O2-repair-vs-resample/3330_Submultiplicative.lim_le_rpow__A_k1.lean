/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Submultiplicative.lim_le_rpow
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Subadditive.lean, line 47
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem lim_le_rpow (hbdd : ∀ n, 0 ≤ u n) {n : ℕ} (hn : n ≠ 0) : h.lim ≤ u n ^ (n : ℝ)⁻¹ := by
  unfold Submultiplicative.lim
  refine csInf_le ?_ ?_
  · exact ⟨0, by rintro _ ⟨m, -, rfl⟩; exact Real.rpow_nonneg (hbdd m) _⟩
  · exact mem_image_of_mem _ (show n ∈ Ici 1 from Nat.one_le_iff_ne_zero.mpr hn)
