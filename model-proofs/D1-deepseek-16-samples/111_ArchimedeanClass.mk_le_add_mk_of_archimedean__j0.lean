/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ArchimedeanClass.mk_le_add_mk_of_archimedean
Source:      Mathlib @ d0a050ad6, Mathlib/Algebra/Order/Ring/Archimedean.lean, line 164 (group STABLE)
Experiment:  D1-deepseek-16-samples, arm sample 0, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 16 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
theorem mk_le_add_mk_of_archimedean [Archimedean S] (f : S →+*o R) (x : R) (y : S) :
    mk x ≤ mk x + mk (f y) := by
  rw [add_comm]
  apply mk_le_mk_add_of_archimedean
