/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable
Source:      Mathlib @ d0a050ad6, Mathlib/Combinatorics/SimpleGraph/LapMatrix.lean, line 219 (group STABLE)
Experiment:  UE1-deepseek-8-samples, arm sample 1, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
theorem lapMatrix_mulVec_eq_zero_iff_forall_reachable {x : V → ℝ} :
    G.lapMatrix ℝ *ᵥ x = 0 ↔ ∀ i j : V, G.Reachable i j → x i = x j := by
  rw [← (posSemidef_lapMatrix ℝ G).toLinearMap₂'_zero_iff, star_trivial,
      lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable]
