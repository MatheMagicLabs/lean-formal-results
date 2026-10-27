/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Finset.Ico_succ_succ
Source:      Mathlib @ d0a050ad6, Mathlib/Data/Int/Interval.lean, line 182 (group DRIFT)
Experiment:  D1-deepseek-16-samples, arm sample 0, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 16 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
lemma Finset.Ico_succ_succ (m n : ℕ) :
    Ico (-(m + 1) : ℤ) (n + 1) = Ico (-m : ℤ) n ∪ {(-(m + 1) : ℤ), (n : ℤ)} := by
  ext
  simp only [mem_Ico, union_insert, union_singleton, mem_insert]
  omega
