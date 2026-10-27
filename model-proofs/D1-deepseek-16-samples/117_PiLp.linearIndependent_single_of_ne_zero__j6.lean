/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     PiLp.linearIndependent_single_of_ne_zero
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/Normed/Lp/PiLp.lean, line 222 (group STABLE)
Experiment:  D1-deepseek-16-samples, arm sample 6, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 16 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
theorem linearIndependent_single_of_ne_zero [Ring 𝕜] [IsDomain 𝕜] {M : Type*}
    [AddCommGroup M] [Module 𝕜 M] [IsTorsionFree 𝕜 M] {v : ι → M} (hv : ∀ i, v i ≠ 0) :
    LinearIndependent 𝕜 fun i : ι ↦ single p i (v i) := by
  suffices LinearIndependent 𝕜 ((WithLp.linearEquiv p 𝕜 _).symm.toLinearMap ∘
      fun i : ι ↦ Pi.single i (v i)) by
    simpa
  rw [LinearMap.linearIndependent_iff_of_injOn _ (by simp)]
  exact Pi.linearIndependent_single_of_ne_zero hv
