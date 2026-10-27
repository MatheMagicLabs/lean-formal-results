/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     inner_vsub_vsub_right_eq_dist_sq_left_iff
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/InnerProductSpace/Affine.lean, line 56 (group DRIFT)
Experiment:  D1-deepseek-16-samples, arm sample 11, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 16 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
theorem inner_vsub_vsub_right_eq_dist_sq_left_iff {a b c : P} :
    ⟪a -ᵥ c, b -ᵥ c⟫ = dist a c ^ 2 ↔ ⟪a -ᵥ c, b -ᵥ a⟫ = 0 := by
  rw [dist_eq_norm_vsub V, inner_eq_norm_sq_left_iff, vsub_sub_vsub_cancel_right,
    inner_vsub_right_eq_zero_symm]
