/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Meromorphic.meromorphic_comp_sub_const_iff_meromorphic
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/Meromorphic/Basic.lean, line 923 (group STABLE)
Experiment:  UE1-deepseek-8-samples, arm sample 0, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
@[simp] theorem meromorphic_comp_sub_const_iff_meromorphic {c : 𝕜} :
    Meromorphic (f ∘ (· - c)) ↔ Meromorphic f := by
  rw [show f ∘ (· - c) = f ∘ ((· + (-c)) : 𝕜 → 𝕜) by ext1 z; simp [sub_eq_add_neg, add_comm]]
  simp [meromorphic_comp_add_const_iff_meromorphic]
