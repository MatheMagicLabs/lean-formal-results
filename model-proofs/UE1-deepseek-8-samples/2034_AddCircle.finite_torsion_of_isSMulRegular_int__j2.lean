/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AddCircle.finite_torsion_of_isSMulRegular_int
Source:      Mathlib @ d0a050ad6, Mathlib/Topology/Instances/AddCircle/Defs.lean, line 270 (group DRIFT)
Experiment:  UE1-deepseek-8-samples, arm sample 2, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
theorem finite_torsion_of_isSMulRegular_int (n : ℤ) (hn : IsSMulRegular 𝕜 n) :
    {x : AddCircle p | n • x = 0}.Finite := by
  nontriviality 𝕜
  obtain rfl | h0 := eq_or_ne n 0
  exacts [hn.not_zero.elim, ENat.card_lt_top.mp <|
    (card_torsion_le_of_isSMulRegular_int p n h0 hn).trans_lt <| ENat.natCast_lt_top _]
