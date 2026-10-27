/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.locallyIntegrableOn_neg_iff
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Function/LocallyIntegrable.lean, line 217 (group DRIFT)
Experiment:  UE1-deepseek-8-samples, arm sample 7, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
@[simp] theorem locallyIntegrableOn_neg_iff {f : X → E} :
    LocallyIntegrableOn (-f) s μ ↔ LocallyIntegrableOn f s μ := by
  constructor <;> intro h
  <;> simpa using h.neg
