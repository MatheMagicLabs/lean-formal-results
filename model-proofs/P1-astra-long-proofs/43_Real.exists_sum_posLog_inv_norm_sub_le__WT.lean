/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.exists_sum_posLog_inv_norm_sub_le
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/Complex/ValueDistribution/SecondMainTheorem.lean, line 56
             (added after the model's training data; human proof 67 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 1 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem exists_sum_posLog_inv_norm_sub_le (s : Finset 𝕜) :
    ∃ C, ∀ w : 𝕜, ∑ a ∈ s, log⁺ ‖w - a‖⁻¹ ≤ log⁺ ‖∑ a ∈ s, (w - a)⁻¹‖ + C := by
  classical
  by_cases hs : (s : Set 𝕜).Nontrivial
  swap
  · have hcard := Finset.card_le_one_iff_subsingleton.mpr (Set.not_nontrivial_iff.mp hs); obtain ⟨a, ha⟩ := Finset.card_le_one_iff_subset_singleton.mp hcard; rcases Finset.subset_singleton_iff.mp ha with rfl | rfl <;> refine ⟨0, ?_⟩ <;> intro w <;> simp [norm_inv]
  let c : ℝ := (s : Set 𝕜).infsep / 2
  have hc : 0 < c := div_pos ((s.infsep_pos_iff_nontrivial).mpr hs) (by norm_num)
  let B : ℝ := (s.card : ℝ) * log⁺ c⁻¹
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) posLog_nonneg
  have hn : 0 ≤ (s.card : ℝ) := Nat.cast_nonneg _
  have htwo : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
  refine ⟨2 * B + s.card + log 2, ?_⟩
  intro w
  by_cases hfar : ∀ a ∈ s, c ≤ ‖w - a‖
  · have hbound := sum_posLog_inv_norm_sub_le hc hfar; have hp : 0 ≤ log⁺ ‖∑ a ∈ s, (w - a)⁻¹‖ := posLog_nonneg; change ∑ a ∈ s, log⁺ ‖w - a‖⁻¹ ≤ B at hbound; linarith
  push_neg at hfar
  obtain ⟨a, ha, hwa⟩ := hfar
  have hdist : ∀ b ∈ s.erase a, c ≤ ‖w - b‖ := by intro b hb; obtain ⟨hba, hbs⟩ := mem_erase.mp hb; have hsep := Set.infsep_le_dist_of_mem (s := (s : Set 𝕜)) ha hbs hba.symm; have htri := dist_triangle a w b; rw [dist_eq_norm] at hsep; rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, norm_sub_rev a w] at htri; dsimp [c] at hwa ⊢; linarith
  have hcard : ((s.erase a).card : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast (Finset.card_erase_le (s := s) (a := a))
  have hrest : ∑ b ∈ s.erase a, log⁺ ‖w - b‖⁻¹ ≤ B := (sum_posLog_inv_norm_sub_le hc hdist).trans (mul_le_mul_of_nonneg_right hcard posLog_nonneg)
  have hlogcard : log ((s.erase a).card : ℝ) ≤ (s.card : ℝ) := (log_le_self (Nat.cast_nonneg _)).trans hcard
  have hnorm : log⁺ ‖∑ b ∈ s.erase a, (w - b)⁻¹‖ ≤ log ((s.erase a).card : ℝ) + ∑ b ∈ s.erase a, log⁺ ‖w - b‖⁻¹ := by simpa only [norm_inv] using posLog_norm_sum_le (s.erase a) (fun b ↦ (w - b)⁻¹)
  have heq : (w - a)⁻¹ = (∑ b ∈ s, (w - b)⁻¹) + -(∑ b ∈ s.erase a, (w - b)⁻¹) := by rw [← add_sum_erase s (fun b ↦ (w - b)⁻¹) ha]; simp
  have hone := posLog_norm_add_le (∑ b ∈ s, (w - b)⁻¹) (-(∑ b ∈ s.erase a, (w - b)⁻¹))
  rw [← heq, norm_neg, norm_inv] at hone
  rw [← add_sum_erase s (fun b ↦ log⁺ ‖w - b‖⁻¹) ha]
  linarith
