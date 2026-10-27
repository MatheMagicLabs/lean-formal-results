/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.mulCayley_adj
Source:      Mathlib @ d0a050ad6, Mathlib/Combinatorics/SimpleGraph/Cayley.lean, line 124 (group STABLE)
Experiment:  D1-deepseek-16-samples, arm sample 3, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 16 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
lemma mulCayley_adj (u v : M) :
    (mulCayley s).Adj u v ↔ u ≠ v ∧ (u⁻¹ * v ∈ s ∨ v⁻¹ * u ∈ s) := by
  simp [mulCayley_adj', mul_left_inj, mul_right_inj, exists_or, or_comm, or_left_comm]
  <;> aesop
