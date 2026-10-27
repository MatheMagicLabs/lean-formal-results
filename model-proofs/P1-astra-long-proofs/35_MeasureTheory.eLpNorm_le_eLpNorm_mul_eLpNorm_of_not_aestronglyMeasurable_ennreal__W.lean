/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_not_aestronglyMeasurable_ennreal
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean, line 199
             (added after the model's training data; human proof 30 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 3 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem eLpNorm_le_eLpNorm_mul_eLpNorm_of_not_aestronglyMeasurable_ennreal
    (p q r : ℝ≥0∞) (b : E → F → G) (c : ℝ≥0∞)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖ₑ ≤ c * ‖f x‖ₑ * ‖g x‖ₑ)
    (hfg : ¬ (AEStronglyMeasurable f μ ∧ AEStronglyMeasurable g μ))
    (hp : p ≠ 0) (hq : q ≠ 0) :
    eLpNorm (fun x => b (f x) (g x)) r μ ≤ c * eLpNorm f p μ * eLpNorm g q μ := by
  classical
  have hz : (∀ᵐ x ∂μ, b (f x) (g x) = 0) → eLpNorm (fun x => b (f x) (g x)) r μ = 0 := by intro hb; simpa using eLpNorm_congr_ae hb
  by_cases hc : c = 0
  · have hb : ∀ᵐ x ∂μ, b (f x) (g x) = 0 := h.mono (fun x hx => by simpa [hc] using hx); rw [hz hb]; exact zero_le
  by_cases hfp : eLpNorm f p μ = 0
  · have hb : ∀ᵐ x ∂μ, b (f x) (g x) = 0 := by { filter_upwards [h, (eLpNorm_eq_zero_iff hp).mp hfp] with x hx hfx; simpa [hfx] using hx }; rw [hz hb]; exact zero_le
  by_cases hgq : eLpNorm g q μ = 0
  · have hb : ∀ᵐ x ∂μ, b (f x) (g x) = 0 := by { filter_upwards [h, (eLpNorm_eq_zero_iff hq).mp hgq] with x hx hgx; simpa [hgx] using hx }; rw [hz hb]; exact zero_le
  by_cases hf : AEStronglyMeasurable f μ
  · have hg : ¬ AEStronglyMeasurable g μ := fun hg => hfg ⟨hf, hg⟩; simp [eLpNorm_of_not_aestronglyMeasurable hg, hc, hfp]
  · simp [eLpNorm_of_not_aestronglyMeasurable hf, hc, hgq]
