/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ContMDiff.congr
Source:      Mathlib @ d0a050ad6, Mathlib/Geometry/Manifold/ContMDiff/Defs.lean, line 916 (group STABLE)
Experiment:  D1-deepseek-16-samples, arm sample 14, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 16 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
theorem ContMDiff.congr (h : ContMDiff I I' n f) (h₁ : ∀ y, f₁ y = f y) :
    ContMDiff I I' n f₁ := by
  rw [show f₁ = f by funext y; apply h₁ y]
  exact h
