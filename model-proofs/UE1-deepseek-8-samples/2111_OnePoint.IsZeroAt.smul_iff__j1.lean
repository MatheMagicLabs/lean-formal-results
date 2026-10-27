/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     OnePoint.IsZeroAt.smul_iff
Source:      Mathlib @ d0a050ad6, Mathlib/NumberTheory/ModularForms/BoundedAtCusp.lean, line 62 (group STABLE)
Experiment:  UE1-deepseek-8-samples, arm sample 1, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
lemma IsZeroAt.smul_iff : IsZeroAt (g • c) f k ↔ IsZeroAt c (f ∣[k] g) k := by
  rw [IsZeroAt, IsZeroAt, (Equiv.mulLeft g⁻¹).forall_congr_left]
  simp [mul_smul, ← SlashAction.slash_mul]
