/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     DihedralGroup.center_eq_closure_of_even_ne_two
Source:      Mathlib @ d0a050ad6, Mathlib/GroupTheory/SpecificGroups/Dihedral.lean, line 317
             (added after the model's training data; human proof 27 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 8 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem center_eq_closure_of_even_ne_two (heven : Even n) (hn2 : n ≠ 2) :
    Subgroup.center (DihedralGroup n) = Subgroup.zpowers (r (n / 2 : ℕ)) := by
  apply le_antisymm
  · intro x hx; rw [Subgroup.mem_center_iff] at hx; rcases x with i | i; { have hi : i + i = 0 := by { have h := hx (sr 0); simpa only [sr_mul_r, r_mul_sr, zero_add, add_zero, zero_sub, sr.injEq, neg_eq_iff_add_eq_zero, eq_neg_iff_add_eq_zero] using h }; by_cases hn0 : n = 0; { subst n; change ℤ at i; change i + i = (0 : ℤ) at hi; have hi0 : i = (0 : ℤ) := by { omega }; rw [hi0]; change (1 : DihedralGroup 0) ∈ Subgroup.zpowers (r (0 / 2 : ℕ)); exact Subgroup.one_mem _ }; letI : NeZero n := ⟨hn0⟩; have hv : (i.val + i.val) % n = 0 := by { have h := congrArg ZMod.val hi; simpa only [ZMod.val_add, ZMod.val_zero] using h }; have hlt := ZMod.val_lt i; have hs : i.val + i.val = 0 ∨ i.val + i.val = n := by { by_cases h : i.val + i.val < n; { left; rwa [Nat.mod_eq_of_lt h] at hv }; right; have hsub : i.val + i.val - n < n := by { omega }; have heq : i.val + i.val - n + n = i.val + i.val := Nat.sub_add_cancel (by omega); have he := congrArg (fun k : ℕ => k % n) heq; have he' : (i.val + i.val - n) % n = 0 := by { simpa only [Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod] using he.trans hv }; rw [Nat.mod_eq_of_lt hsub] at he'; omega }; have hhalf : n / 2 + n / 2 = n := by { obtain ⟨k, hk⟩ := heven; omega }; have hv' : i.val = 0 ∨ i.val = n / 2 := by { omega }; rcases hv' with h | h; { have hi0 : i = 0 := by { simpa only [h, Nat.cast_zero] using (ZMod.natCast_zmod_val i).symm }; simpa only [hi0, r_zero] using (Subgroup.one_mem (Subgroup.zpowers (r (n / 2 : ℕ) : DihedralGroup n))) }; have hi' : i = (n / 2 : ℕ) := by { rw [← ZMod.natCast_zmod_val i, h] }; exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp only [zpow_one, hi']⟩ }; have h := hx (r 1); have htwo : (2 : ZMod n) = 0 := by { have h' : (1 : ZMod n) + 1 = 0 := by { simpa only [r_mul_sr, sr_mul_r, sr.injEq, sub_eq_add_neg, add_left_cancel_iff, neg_eq_iff_add_eq_zero, eq_neg_iff_add_eq_zero] using h }; simpa only [one_add_one_eq_two] using h' }; have hmod : 2 % n = 0 := by { have h' := congrArg ZMod.val htwo; simpa only [ZMod.val_two_eq_two_mod, ZMod.val_zero] using h' }; have hle := Nat.le_of_dvd (by decide : 0 < 2) (Nat.dvd_of_mod_eq_zero hmod); have hn0 : n ≠ 0 := by { intro hn0; subst n; norm_num at hmod }; obtain ⟨k, hk⟩ := heven; omega
  · apply Subgroup.zpowers_le.mpr; rw [Subgroup.mem_center_iff]; have hhalf : n / 2 + n / 2 = n := by { obtain ⟨k, hk⟩ := heven; omega }; have hh : (↑(n / 2) : ZMod n) + ↑(n / 2) = 0 := by { rw [← Nat.cast_add, hhalf] <;> simp }; have hneg : -(↑(n / 2) : ZMod n) = ↑(n / 2) := neg_eq_iff_add_eq_zero.mpr hh; rintro (i | i) <;> simp [sub_eq_add_neg, hneg, add_comm]
