/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.exists_sum_posLog_inv_norm_sub_le
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/Complex/ValueDistribution/SecondMainTheorem.lean, line 56
             (added after the model's training data; human proof 67 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 5 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem exists_sum_posLog_inv_norm_sub_le (s : Finset 𝕜) :
    ∃ C, ∀ w : 𝕜, ∑ a ∈ s, log⁺ ‖w - a‖⁻¹ ≤ log⁺ ‖∑ a ∈ s, (w - a)⁻¹‖ + C := by
  classical
  have hmin : ∀ t : Finset ℝ, (∀ x ∈ t, 0 < x) → ∃ d, 0 < d ∧ ∀ x ∈ t, d ≤ x := by { intro t; induction t using Finset.induction_on with | empty => intro h; exact ⟨1, by norm_num, by simp⟩ | @insert x t hx ih => intro h; obtain ⟨d, hd, hdt⟩ := ih (fun y hy => h y (mem_insert_of_mem hy)); refine ⟨min x d, lt_min (h x (mem_insert_self _ _)) hd, ?_⟩; intro y hy; rcases mem_insert.mp hy with rfl | hy; exact min_le_left _ _; exact le_trans (min_le_right _ _) (hdt y hy) }
  have hlog : ∀ x y B : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ B → x ≤ y + B → log⁺ x ≤ log⁺ y + log (B + 1) := by {
  intro x y B hx hy hB hxy
  have hp₀ : 0 ≤ log⁺ y := by { simp [posLog] }
  have hp₁ : log y ≤ log⁺ y := by { simp [posLog] }
  have hB₁ : 0 < B + 1 := by { linarith }
  have hLB : 0 ≤ log (B + 1) := log_nonneg (by linarith)
  have hLX : log x ≤ log⁺ y + log (B + 1) := by {
  by_cases hx₀ : x = 0
  · simpa only [hx₀, log_zero] using add_nonneg hp₀ hLB
  have hx₁ : 0 < x := lt_of_le_of_ne hx (Ne.symm hx₀)
  by_cases hy₁ : y ≤ 1
  · have h := log_le_log hx₁ (show x ≤ B + 1 by linarith); linarith
  have hy₂ : 0 < y := by { linarith }
  have hmul : x ≤ y * (B + 1) := by { nlinarith }
  have h := log_le_log hx₁ hmul
  rw [log_mul (ne_of_gt hy₂) (ne_of_gt hB₁)] at h
  linarith }
  simp only [posLog] at hp₀ hLX ⊢
  exact max_le (add_nonneg hp₀ hLB) hLX }
  let t : Finset ℝ := ((s.product s).filter (fun p => p.1 ≠ p.2)).image (fun p => ‖p.1 - p.2‖)
  have ht : ∀ x ∈ t, 0 < x := by { intro x hx; rcases mem_image.mp hx with ⟨⟨a, b⟩, hab, rfl⟩; simp only [mem_filter, mem_product] at hab; exact norm_pos_iff.mpr (sub_ne_zero.mpr hab.2) }
  obtain ⟨δ, hδ, hd⟩ := hmin t ht
  have hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → δ ≤ ‖a - b‖ := by { intro a ha b hb hab; apply hd; exact mem_image.mpr ⟨(a, b), by simp [ha, hb, hab], rfl⟩ }
  let D : ℝ := δ / 2
  have hD : 0 < D := by { dsimp [D]; positivity }
  let B : ℝ := (s.card : ℝ) * D⁻¹
  have hB : 0 ≤ B := by { dsimp [B]; positivity }
  have hLB : 0 ≤ log (B + 1) := log_nonneg (by linarith)
  refine ⟨(s.card : ℝ) * log⁺ D⁻¹ + log (B + 1), ?_⟩
  intro w
  have hp : 0 ≤ log⁺ ‖∑ a ∈ s, (w - a)⁻¹‖ := by { simp [posLog] }
  by_cases hw : ∀ a ∈ s, D ≤ ‖w - a‖
  · have h := sum_posLog_inv_norm_sub_le hD hw; linarith
  push_neg at hw
  obtain ⟨a, ha, hwa⟩ := hw
  have he : ∀ b ∈ s.erase a, D ≤ ‖w - b‖ := by { intro b hb; have hb' := mem_erase.mp hb; have hs := hsep a ha b hb'.2 (Ne.symm hb'.1); have hn := norm_add_le (a - w) (w - b); rw [sub_add_sub_cancel, norm_sub_rev a w] at hn; dsimp [D] at *; linarith }
  have hcard : ((s.erase a).card : ℝ) ≤ (s.card : ℝ) := by { exact_mod_cast card_le_card (erase_subset a s) }
  have hrest : ‖∑ b ∈ s.erase a, (w - b)⁻¹‖ ≤ B := by {
  calc
  ‖∑ b ∈ s.erase a, (w - b)⁻¹‖ ≤ ∑ b ∈ s.erase a, ‖(w - b)⁻¹‖ := norm_sum_le _ _
  _ ≤ ∑ b ∈ s.erase a, D⁻¹ := sum_le_sum (fun b hb => by { rw [norm_inv]; gcongr; exact he b hb })
  _ = ((s.erase a).card : ℝ) * D⁻¹ := by rw [sum_const, nsmul_eq_mul]
  _ ≤ B := mul_le_mul_of_nonneg_right hcard (by positivity) }
  have hrestlog : ∑ b ∈ s.erase a, log⁺ ‖w - b‖⁻¹ ≤ (s.card : ℝ) * log⁺ D⁻¹ := (sum_posLog_inv_norm_sub_le hD he).trans (mul_le_mul_of_nonneg_right hcard (by simp [posLog]))
  have hs : (∑ b ∈ s.erase a, (w - b)⁻¹) + (w - a)⁻¹ = ∑ b ∈ s, (w - b)⁻¹ := sum_erase_add s (fun b => (w - b)⁻¹) ha
  have hid : (∑ b ∈ s, (w - b)⁻¹) - (∑ b ∈ s.erase a, (w - b)⁻¹) = (w - a)⁻¹ := by { rw [← hs]; simp }
  have hn := norm_sub_le (∑ b ∈ s, (w - b)⁻¹) (∑ b ∈ s.erase a, (w - b)⁻¹)
  rw [hid, norm_inv] at hn
  have hx : ‖w - a‖⁻¹ ≤ ‖∑ b ∈ s, (w - b)⁻¹‖ + B := by { linarith [hrest] }
  have hl := hlog ‖w - a‖⁻¹ ‖∑ b ∈ s, (w - b)⁻¹‖ B (by positivity) (norm_nonneg _) hB hx
  have hsplit : (∑ b ∈ s.erase a, log⁺ ‖w - b‖⁻¹) + log⁺ ‖w - a‖⁻¹ = ∑ b ∈ s, log⁺ ‖w - b‖⁻¹ := sum_erase_add s (fun b => log⁺ ‖w - b‖⁻¹) ha
  linarith
