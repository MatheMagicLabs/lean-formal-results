/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     DihedralGroup.center_eq_closure_of_even_ne_two
Source:      Mathlib @ d0a050ad6, Mathlib/GroupTheory/SpecificGroups/Dihedral.lean, line 317
             (added after the model's training data; human proof 27 tactic steps)
Experiment:  P1-astra-long-proofs, arm P, solved after 4 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem center_eq_closure_of_even_ne_two (heven : Even n) (hn2 : n ≠ 2) :
    Subgroup.center (DihedralGroup n) = Subgroup.zpowers (r (n / 2 : ℕ)) := by
  have hcenter : ∀ g : DihedralGroup n,
      g ∈ Subgroup.center (DihedralGroup n) ↔
        ∃ i : ZMod n, g = r i ∧ i + i = 0 := by
    intro g
    constructor
    · intro hg
      have hg' := Subgroup.mem_center_iff.mp hg
      cases g with
      | r i =>
        refine ⟨i, rfl, ?_⟩
        simpa using sr.inj (hg' (sr i))
      | sr i =>
        have h := sr.inj (hg' (r 1))
        have hneg : -(1 : ZMod n) = 1 := by
          apply add_left_cancel (a := i)
          simpa only [sub_eq_add_neg] using h
        have htwo : (2 : ZMod n) = 0 := by
          simpa only [one_add_one_eq_two] using
            (neg_eq_iff_add_eq_zero.mp hneg)
        rw [← ZMod.val_eq_zero, ZMod.val_two_eq_two_mod] at htwo
        have hd : n ∣ 2 := Nat.dvd_of_mod_eq_zero htwo
        have hle : n ≤ 2 := Nat.le_of_dvd Nat.zero_lt_two hd
        have hn0 : n ≠ 0 := by
          rintro rfl
          norm_num at hd
        obtain ⟨k, hk⟩ := heven
        omega
    · rintro ⟨i, rfl, hi⟩
      have hneg : -i = i := neg_eq_iff_add_eq_zero.mpr hi
      apply Subgroup.mem_center_iff.mpr
      rintro (j | j) <;>
        simp [sub_eq_add_neg, hneg, add_comm]
  have hzpowers : ∀ g : DihedralGroup n,
      g ∈ Subgroup.zpowers (r (n / 2 : ℕ)) ↔
        ∃ i : ZMod n, g = r i ∧ i + i = 0 := by
    have hnat : n / 2 + n / 2 = n := by
      obtain ⟨k, hk⟩ := heven
      omega
    have hhalf : (n / 2 : ℕ) + (n / 2 : ℕ) = (0 : ZMod n) := by
      rw [← Nat.cast_add, hnat]
      simp
    intro g
    constructor
    · intro hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      refine ⟨_, r_zpow _ _, ?_⟩
      rw [← add_mul, hhalf, zero_mul]
    · rintro ⟨i, rfl, hi⟩
      by_cases hn : n = 0
      · subst n
        have hz : ∀ z : ℤ, z + z = 0 → z = 0 := by omega
        have hi0 : i = 0 := hz i hi
        apply Subgroup.mem_zpowers_iff.mpr
        exact ⟨0, by simp [hi0]⟩
      · letI : NeZero n := ⟨hn⟩
        have hmod : (i.val + i.val) % n = 0 := by
          have hz : ((i.val + i.val : ℕ) : ZMod n) = 0 := by
            simpa using hi
          rw [← ZMod.val_eq_zero, ZMod.val_natCast] at hz
          exact hz
        have hlt := ZMod.val_lt i
        have hv : i.val = 0 ∨ i.val = n / 2 := by
          by_cases hs : i.val + i.val < n
          · rw [Nat.mod_eq_of_lt hs] at hmod
            left
            omega
          · have hs' : i.val + i.val - n < n := by omega
            rw [Nat.mod_eq_sub_mod (by omega : n ≤ i.val + i.val),
              Nat.mod_eq_of_lt hs'] at hmod
            right
            omega
        rcases hv with hv | hv
        · have hi0 : i = 0 := by
            rw [← ZMod.natCast_zmod_val i, hv]
            simp
          apply Subgroup.mem_zpowers_iff.mpr
          exact ⟨0, by simp [hi0]⟩
        · have hihalf : i = (n / 2 : ℕ) := by
            rw [← ZMod.natCast_zmod_val i, hv]
          apply Subgroup.mem_zpowers_iff.mpr
          exact ⟨1, by simp [hihalf]⟩
  ext g
  exact (hcenter g).trans (hzpowers g).symm
