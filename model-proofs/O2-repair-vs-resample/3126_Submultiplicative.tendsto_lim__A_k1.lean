/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Submultiplicative.tendsto_lim
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Subadditive.lean, line 89
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem tendsto_lim (hbdd : ∀ n, 0 ≤ u n) : Tendsto (fun n ↦ u n ^ (n : ℝ)⁻¹) atTop (𝓝 h.lim) := by
  refine tendsto_order.2 ⟨fun l hl => ?_, fun L hL => ?_⟩
  · exact eventually_atTop.2
      ⟨1, fun n hn => hl.trans_le (h.lim_le_rpow hbdd (by omega))⟩
  · obtain ⟨n, npos, hn⟩ : ∃ n : ℕ, 0 < n ∧ u n ^ (n : ℝ)⁻¹ < L := by
      rw [Submultiplicative.lim] at hL
      rcases exists_lt_of_csInf_lt (nonempty_Ici.image _) hL with ⟨x, hx, xL⟩
      rcases (mem_image _ _ _).1 hx with ⟨n, hn, rfl⟩
      exact ⟨n, zero_lt_one.trans_le hn, xL⟩
    exact h.eventually_rpow_lt_of_rpow_lt hbdd npos.ne' hn
