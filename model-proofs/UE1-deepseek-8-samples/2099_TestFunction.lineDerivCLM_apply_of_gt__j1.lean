/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     TestFunction.lineDerivCLM_apply_of_gt
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/Distribution/TestFunction.lean, line 590 (group STABLE)
Experiment:  UE1-deepseek-8-samples, arm sample 1, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
lemma lineDerivCLM_apply_of_gt {v : E} (hk : n < k + 1) :
    (lineDerivCLM 𝕜 v : 𝓓^{n}(Ω, F) →L[𝕜] 𝓓^{k}(Ω, F)) = 0 := by
  ext
  simp [hk]
