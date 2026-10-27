/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.condExp_bilin_of_aestronglyMeasurable_right
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Function/ConditionalExpectation/PullOut.lean, line 215 (group STABLE)
Experiment:  D1-deepseek-16-samples, arm sample 1, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 16 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
theorem condExp_bilin_of_aestronglyMeasurable_right [CompleteSpace F] {f : Ω → F} {g : Ω → E}
    (hg : AEStronglyMeasurable[m] g μ)
    (hfg : Integrable (fun ω ↦ B (f ω) (g ω)) μ) (hf : Integrable f μ) :
    μ[fun ω ↦ B (f ω) (g ω) | m] =ᵐ[μ] fun ω ↦ B (μ[f | m] ω) (g ω) := by
  simp_rw [← B.flip_apply] at hfg ⊢
  apply condExp_bilin_of_aestronglyMeasurable_left B.flip hg hfg hf
