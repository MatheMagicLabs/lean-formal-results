/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     DihedralGroup.center_eq_closure_of_even_ne_two
Source:      Mathlib @ d0a050ad6, Mathlib/GroupTheory/SpecificGroups/Dihedral.lean, line 317
             (added after the model's training data; human proof 27 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 2 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem center_eq_closure_of_even_ne_two (heven : Even n) (hn2 : n ≠ 2) :
    Subgroup.center (DihedralGroup n) = Subgroup.zpowers (r (n / 2 : ℕ)) := by
  have hn1 : n ≠ 1 := by rintro rfl; simpa using heven
  have hhalf : n / 2 + n / 2 = n := by obtain ⟨k, hk⟩ := heven; omega
  apply le_antisymm
  · intro x hx; have h := Subgroup.mem_center_iff.mp hx; cases x with
  | r i => have hi : -i = i := by simpa using (sr.inj (h (sr 0))).symm
           rcases (ZMod.neg_eq_self_iff i).mp hi with hi | hi
           · simpa [hi] using (Subgroup.zpowers (r (n / 2 : ℕ))).one_mem
           · by_cases hn0 : n = 0
             · have hiv : i.val = 0 := by omega
               have hiz := (ZMod.val_eq_zero i).mp hiv
               simpa [hiz] using (Subgroup.zpowers (r (n / 2 : ℕ))).one_mem
             · letI : NeZero n := ⟨hn0⟩
               have hiv : i.val = n / 2 := by omega
               rw [← ZMod.natCast_zmod_val i, hiv]
               exact Subgroup.mem_zpowers _
  | sr i => have hi : (-1 : ZMod n) = 1 := by apply add_left_cancel (a := i); simpa [sub_eq_add_neg] using sr.inj (h (r 1))
            exact ((ZMod.neg_one_eq_one_iff.mp hi).elim hn1 hn2).elim
  · apply Subgroup.zpowers_le.mpr; apply Subgroup.mem_center_iff.mpr; have hz : ((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n) = 0 := by rw [← Nat.cast_add, hhalf]; simp
    have hneg : -((n / 2 : ℕ) : ZMod n) = ((n / 2 : ℕ) : ZMod n) := neg_eq_iff_add_eq_zero.mpr hz
    rintro (i | i) <;> simp [add_comm, sub_eq_add_neg, hneg]
