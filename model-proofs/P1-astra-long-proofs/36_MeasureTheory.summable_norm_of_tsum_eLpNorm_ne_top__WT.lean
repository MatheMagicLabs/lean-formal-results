/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.summable_norm_of_tsum_eLpNorm_ne_top
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Function/LpSpace/InfiniteSum.lean, line 30
             (added after the model's training data; human proof 58 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 3 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem summable_norm_of_tsum_eLpNorm_ne_top {ι : Type*} [Countable ι]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ι → X → E} (h'f : ∑' n, eLpNorm (f n) p μ ≠ ∞) :
    ∀ᵐ a ∂μ, Summable (fun n ↦ ‖f n a‖) := by
  classical
  have hf : ∀ i, AEStronglyMeasurable (f i) μ := fun i =>
    aestronglyMeasurable_of_eLpNorm_ne_top
      (ne_top_of_le_ne_top h'f
        (ENNReal.le_tsum (f := fun j => eLpNorm (f j) p μ) i))
  obtain ⟨s, _, hs⟩ := exists_seq_monotone_tendsto_atTop_atTop (Finset ι)
  let g : ℕ → X → ℝ := fun n x => ∑ i ∈ s n, ‖f i x‖
  have hb : ∀ n, eLpNorm (g n) p μ ≤
      ((∑' i, eLpNorm (f i) p μ).toNNReal : ℝ≥0∞) := by
    intro n
    rw [ENNReal.coe_toNNReal h'f]
    have hgn : g n = ∑ i ∈ s n, (fun x => ‖f i x‖) := by
      ext x
      simp [g]
    calc
      eLpNorm (g n) p μ ≤ ∑ i ∈ s n, eLpNorm (fun x => ‖f i x‖) p μ := by
        rw [hgn]
        exact eLpNorm_sum_le hp
      _ = ∑ i ∈ s n, eLpNorm (f i) p μ := by
        simp only [eLpNorm_norm _ (hf _)]
      _ ≤ ∑' i, eLpNorm (f i) p μ := ENNReal.sum_le_tsum _
  have hg := ae_bdd_liminf_atTop_of_eLpNorm_bdd
    (zero_lt_one.trans_le hp).ne' hb
  filter_upwards [hg] with x hx
  have he : ∀ n, ‖g n x‖ₑ = ∑ i ∈ s n, ‖f i x‖ₑ := by
    intro n
    dsimp [g]
    simp_rw [← ofReal_norm]
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
    exact ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _)
  have ht : Tendsto (fun n => ‖g n x‖ₑ) atTop (𝓝 (∑' i, ‖f i x‖ₑ)) := by
    simp_rw [he]
    exact ENNReal.summable.hasSum.comp hs
  rw [ht.liminf_eq] at hx
  exact tsum_enorm_ne_top_iff_summable_norm.mp hx.ne
