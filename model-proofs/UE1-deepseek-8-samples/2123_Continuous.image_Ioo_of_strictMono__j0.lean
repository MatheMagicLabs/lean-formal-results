/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Continuous.image_Ioo_of_strictMono
Source:      Mathlib @ d0a050ad6, Mathlib/Topology/Order/IntermediateValue.lean, line 994 (group STABLE)
Experiment:  UE1-deepseek-8-samples, arm sample 0, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
theorem Continuous.image_Ioo_of_strictMono (hf_c : Continuous f) (hf : StrictMono f) :
    f '' Ioo a b = Ioo (f a) (f b) := by
  rcases le_or_gt a b with hab | hab
  · exact hf_c.continuousOn.image_Ioo_of_strictMonoOn hab (hf.strictMonoOn _)
  · simp [lt_asymm hab, lt_asymm (hf hab)]
