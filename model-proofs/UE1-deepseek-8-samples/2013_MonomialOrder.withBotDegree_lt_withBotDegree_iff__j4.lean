/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MonomialOrder.withBotDegree_lt_withBotDegree_iff
Source:      Mathlib @ d0a050ad6, Mathlib/RingTheory/MvPolynomial/MonomialOrder.lean, line 1063 (group DRIFT)
Experiment:  UE1-deepseek-8-samples, arm sample 4, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
lemma withBotDegree_lt_withBotDegree_iff :
    m.withBotDegree f ≺'[m] m.withBotDegree g ↔
      (m.degree f ≺[m] m.degree g ∨ (f = 0 ∧ g ≠ 0)) := by
  classical
  by_cases! hf : f = 0 <;> by_cases! hg : g = 0 <;> simp [withBotDegree_eq, hf, hg, m.toWithBotSyn_apply]
  <;> aesop
