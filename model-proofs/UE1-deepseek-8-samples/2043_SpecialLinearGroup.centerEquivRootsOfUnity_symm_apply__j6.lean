/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SpecialLinearGroup.centerEquivRootsOfUnity_symm_apply
Source:      Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/SpecialLinearGroup.lean, line 526 (group DRIFT)
Experiment:  UE1-deepseek-8-samples, arm sample 6, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
theorem centerEquivRootsOfUnity_symm_apply
    (r : rootsOfUnity (max (Module.finrank R V) 1) R) :
    (centerEquivRootsOfUnity.symm r : V →ₗ[R] V) = r • LinearMap.id := by
  simp [centerEquivRootsOfUnity_apply]
  <;> aesop
