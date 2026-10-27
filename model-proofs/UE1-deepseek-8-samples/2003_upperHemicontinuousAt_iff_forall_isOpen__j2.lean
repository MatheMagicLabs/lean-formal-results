/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     upperHemicontinuousAt_iff_forall_isOpen
Source:      Mathlib @ d0a050ad6, Mathlib/Topology/Semicontinuity/Hemicontinuity.lean, line 54 (group DRIFT)
Experiment:  UE1-deepseek-8-samples, arm sample 2, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
lemma upperHemicontinuousAt_iff_forall_isOpen :
    UpperHemicontinuousAt f x ↔ ∀ u, IsOpen u → f x ⊆ u → ∀ᶠ x' in 𝓝 x, f x' ⊆ u := by
  simp_rw [← upperHemicontinuousWithinAt_univ_iff, upperHemicontinuousWithinAt_iff_forall_isOpen]
  <;> simp
  <;> aesop
