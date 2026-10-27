/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     isMinOn_Icc_of_deriv
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/Calculus/DerivativeTest.lean, line 225 (group DRIFT)
Experiment:  UE1-deepseek-8-samples, arm sample 0, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
lemma isMinOn_Icc_of_deriv {f : ℝ → ℝ} {a b c : ℝ} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
    (hc : ContinuousAt f c) (hd₀ : DifferentiableOn ℝ f (Ioo a b))
    (hd₁ : DifferentiableOn ℝ f (Ioo b c)) (h₀ : ∀ x ∈ Ioo a b, deriv f x ≤ 0)
    (h₁ : ∀ x ∈ Ioo b c, 0 ≤ deriv f x) : IsMinOn f (Icc a c) b := by
  refine isMinOn_Icc_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all
