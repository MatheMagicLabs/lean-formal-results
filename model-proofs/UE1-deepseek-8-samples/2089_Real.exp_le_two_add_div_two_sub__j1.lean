/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.exp_le_two_add_div_two_sub
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/Complex/Exponential.lean, line 676 (group STABLE)
Experiment:  UE1-deepseek-8-samples, arm sample 1, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
lemma exp_le_two_add_div_two_sub {x : ℝ} (hx : 0 ≤ x) (hx' : x < 2) :
    exp x ≤ (2 + x) / (2 - x) := by
  rcases eq_or_lt_of_le hx with (rfl | hx)
  · simp
  · exact (exp_lt_two_add_div_two_sub hx hx').le
