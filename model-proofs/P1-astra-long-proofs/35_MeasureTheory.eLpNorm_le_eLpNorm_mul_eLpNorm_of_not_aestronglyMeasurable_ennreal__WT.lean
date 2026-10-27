/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_not_aestronglyMeasurable_ennreal
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean, line 199
             (added after the model's training data; human proof 30 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 2 call(s)
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
  by_cases hc : c = 0
  · have hb : (fun x => b (f x) (g x)) =ᵐ[μ] 0 := by
      filter_upwards [h] with x hx
      exact enorm_eq_zero.mp (le_antisymm (by simpa [hc] using hx) bot_le)
    rw [eLpNorm_eq_zero_of_ae_zero hb]
    exact zero_le
  by_cases hf0 : eLpNorm f p μ = 0
  · have hf := (eLpNorm_eq_zero_iff hp).mp hf0
    have hb : (fun x => b (f x) (g x)) =ᵐ[μ] 0 := by
      filter_upwards [h, hf] with x hx hfx
      exact enorm_eq_zero.mp (le_antisymm (by simpa [hfx] using hx) bot_le)
    rw [eLpNorm_eq_zero_of_ae_zero hb]
    exact zero_le
  by_cases hg0 : eLpNorm g q μ = 0
  · have hg := (eLpNorm_eq_zero_iff hq).mp hg0
    have hb : (fun x => b (f x) (g x)) =ᵐ[μ] 0 := by
      filter_upwards [h, hg] with x hx hgx
      exact enorm_eq_zero.mp (le_antisymm (by simpa [hgx] using hx) bot_le)
    rw [eLpNorm_eq_zero_of_ae_zero hb]
    exact zero_le
  by_cases hf : AEStronglyMeasurable f μ
  · have hg : ¬ AEStronglyMeasurable g μ := fun hg => hfg ⟨hf, hg⟩
    rw [eLpNorm_of_not_aestronglyMeasurable hg,
      ENNReal.mul_top (mul_ne_zero hc hf0)]
    exact le_top
  · rw [eLpNorm_of_not_aestronglyMeasurable hf,
      ENNReal.mul_top hc, ENNReal.top_mul hg0]
    exact le_top
