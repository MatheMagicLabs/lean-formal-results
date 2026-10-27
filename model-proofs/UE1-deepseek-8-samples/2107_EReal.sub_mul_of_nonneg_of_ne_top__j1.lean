/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     EReal.sub_mul_of_nonneg_of_ne_top
Source:      Mathlib @ d0a050ad6, Mathlib/Data/EReal/Operations.lean, line 858 (group STABLE)
Experiment:  UE1-deepseek-8-samples, arm sample 1, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
lemma sub_mul_of_nonneg_of_ne_top {a b c : EReal} (ha : 0 ≤ a) (ha' : a ≠ ⊤) :
    (b - c) * a = b * a - c * a := by
  rw [sub_eq_add_neg, right_distrib_of_nonneg_of_ne_top ha ha']
  simp [← neg_mul, sub_eq_add_neg]
