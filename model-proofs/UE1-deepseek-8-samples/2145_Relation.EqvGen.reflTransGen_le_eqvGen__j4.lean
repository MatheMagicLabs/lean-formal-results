/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Relation.EqvGen.reflTransGen_le_eqvGen
Source:      Mathlib @ d0a050ad6, Mathlib/Logic/Relation.lean, line 882 (group STABLE)
Experiment:  UE1-deepseek-8-samples, arm sample 4, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
lemma reflTransGen_le_eqvGen : ReflTransGen r ≤ EqvGen r := by
  intro _ _ h
  induction h with
  | refl => exact .refl _
  | tail _ _ ih =>
    apply _root_.trans ih
    exact .rel _ _ ‹_›
