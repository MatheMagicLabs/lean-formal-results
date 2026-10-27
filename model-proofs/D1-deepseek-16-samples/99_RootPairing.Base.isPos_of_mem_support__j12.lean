/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     RootPairing.Base.isPos_of_mem_support
Source:      Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/RootSystem/Base.lean, line 563 (group STABLE)
Experiment:  D1-deepseek-16-samples, arm sample 12, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 16 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
lemma isPos_of_mem_support {i : ι} (h : i ∈ b.support) :
    b.IsPos i := by
  rw [isPos_iff]
  exact by
    have h' := b.height_one_of_mem_support h
    simp_all
