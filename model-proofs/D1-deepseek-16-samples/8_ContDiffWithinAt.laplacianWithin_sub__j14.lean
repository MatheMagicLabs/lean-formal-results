/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ContDiffWithinAt.laplacianWithin_sub
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/InnerProductSpace/Laplacian.lean, line 314 (group DRIFT)
Experiment:  D1-deepseek-16-samples, arm sample 14, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 16 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
theorem _root_.ContDiffWithinAt.laplacianWithin_sub (h₁ : ContDiffWithinAt ℝ 2 f₁ s x)
    (h₂ : ContDiffWithinAt ℝ 2 f₂ s x) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    (Δ[s] (f₁ - f₂)) x = (Δ[s] f₁) x - (Δ[s] f₂) x := by
  simp_all [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis,
    iteratedFDerivWithin_sub_apply h₁ h₂ hs hx]
  <;> aesop
