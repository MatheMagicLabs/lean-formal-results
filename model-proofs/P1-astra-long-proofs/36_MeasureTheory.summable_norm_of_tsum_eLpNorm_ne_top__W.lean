/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.summable_norm_of_tsum_eLpNorm_ne_top
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Function/LpSpace/InfiniteSum.lean, line 30
             (added after the model's training data; human proof 58 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 6 call(s)
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
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hf (i : ι) : AEStronglyMeasurable (f i) μ := aestronglyMeasurable_of_eLpNorm_ne_top (ENNReal.ne_top_of_tsum_ne_top h'f i)
  obtain ⟨s, hs⟩ := exists_seq_tendsto (atTop : Filter (Finset ι))
  let g : ℕ → X → ℝ := fun n a ↦ ∑ i ∈ s n, ‖f i a‖
  have hnorm (i : ι) : eLpNorm (fun a ↦ ‖f i a‖) p μ = eLpNorm (f i) p μ := eLpNorm_norm (f i) (hf i)
  have hb (n : ℕ) : eLpNorm (g n) p μ ≤ ((∑' i, eLpNorm (f i) p μ).toNNReal : ℝ≥0∞) := by
  {
  rw [ENNReal.coe_toNNReal h'f]
  refine le_trans ?_ (ENNReal.sum_le_tsum (s n))
  have heq : (∑ i ∈ s n, fun a ↦ ‖f i a‖) = g n := by
  {
  funext a
  simp only [Finset.sum_apply, g]
  }
  have h := eLpNorm_sum_le (μ := μ) (f := fun i a ↦ ‖f i a‖) (s := s n) hp
  rw [heq] at h
  simpa only [hnorm] using h
  }
  filter_upwards [ae_bdd_liminf_atTop_of_eLpNorm_bdd hp0 hb] with a ha
  have hg (n : ℕ) : ‖g n a‖ₑ = ∑ i ∈ s n, ‖f i a‖ₑ := by
  {
  simp only [enorm_eq_nnnorm, ← ENNReal.coe_finset_sum]
  apply congrArg (fun t : NNReal ↦ (t : ℝ≥0∞))
  apply Subtype.ext
  change ‖g n a‖ = ((∑ i ∈ s n, ‖f i a‖₊ : NNReal) : ℝ)
  rw [NNReal.coe_sum]
  change ‖∑ i ∈ s n, ‖f i a‖‖ = ∑ i ∈ s n, ‖f i a‖
  rw [Real.norm_eq_abs]
  exact abs_of_nonneg (Finset.sum_nonneg fun i _ ↦ norm_nonneg (f i a))
  }
  have ht : Tendsto (fun t : Finset ι ↦ ∑ i ∈ t, ‖f i a‖ₑ) atTop (𝓝 (∑' i, ‖f i a‖ₑ)) := ENNReal.summable.hasSum
  have ht' : Tendsto (fun n ↦ ∑ i ∈ s n, ‖f i a‖ₑ) atTop (𝓝 (∑' i, ‖f i a‖ₑ)) := ht.comp hs
  simp only [hg, ht'.liminf_eq] at ha
  simpa using (ENNReal.summable_toReal ha.ne)
