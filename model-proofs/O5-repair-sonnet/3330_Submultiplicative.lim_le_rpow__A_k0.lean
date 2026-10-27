/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Submultiplicative.lim_le_rpow
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Subadditive.lean, line 47
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem lim_le_rpow (hbdd : ∀ n, 0 ≤ u n) {n : ℕ} (hn : n ≠ 0) : h.lim ≤ u n ^ (n : ℝ)⁻¹ := by
  show sInf _ ≤ _
  refine csInf_le ?_ ?_
  · refine ⟨0, ?_⟩
    rintro _ ⟨k, -, rfl⟩
    exact Real.rpow_nonneg (hbdd k) _
  · exact ⟨n, Nat.one_le_iff_ne_zero.mpr hn, rfl⟩
