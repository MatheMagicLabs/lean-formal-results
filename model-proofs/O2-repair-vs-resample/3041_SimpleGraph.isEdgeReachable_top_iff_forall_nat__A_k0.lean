/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.isEdgeReachable_top_iff_forall_nat
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Connectivity/EdgeConnectivity.lean, line 182
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem isEdgeReachable_top_iff_forall_nat :
    G.IsEdgeReachable ⊤ u v ↔ ∀ n : ℕ, G.IsEdgeReachable n u v := by
  refine ⟨fun h n ↦ h.anti le_top, fun h s hs ↦ ?_⟩
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hs.ne
  exact h (n + 1) (by rw [← hn]; exact_mod_cast Nat.lt_succ_self n)
