/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.mem_zpowers_iff_existsUnique_zpow
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/ArchimedeanDensely.lean, line 44
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma Subgroup.mem_zpowers_iff_existsUnique_zpow {G : Type*}
    [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b : G} (ha : a ≠ 1) :
    b ∈ zpowers a ↔ ∃! k : ℤ, a ^ k = b := by
  have inj : ∀ k m : ℤ, a ^ k = a ^ m → k = m := by
    intro k m h
    by_contra hne
    have hn : k - m ≠ 0 := sub_ne_zero.mpr hne
    have h1 : a ^ (k - m) = 1 := by rw [zpow_sub, h, mul_inv_cancel]
    have key : ∀ c : G, 1 < c → ∀ n : ℤ, n ≠ 0 → c ^ n ≠ 1 := by
      intro c hc n hn
      obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg n
      · have : j ≠ 0 := by
          rintro rfl
          simp at hn
        rw [zpow_natCast]
        exact (one_lt_pow' hc this).ne'
      · have : j ≠ 0 := by
          rintro rfl
          simp at hn
        rw [zpow_neg, zpow_natCast]
        intro h
        exact (one_lt_pow' hc this).ne' (inv_eq_one.mp h)
    rcases lt_or_gt_of_ne ha with h2 | h2
    · have h3 : 1 < a⁻¹ := one_lt_inv'.mpr h2
      apply key a⁻¹ h3 (-(k - m)) (neg_ne_zero.mpr hn)
      rw [zpow_neg, inv_zpow, h1, inv_one, inv_one]
    · exact key a h2 _ hn h1
  constructor
  · intro hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ⟨k, hk, fun m hm => inj m k (hm.trans hk.symm)⟩
  · rintro ⟨k, hk, _⟩
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, hk⟩
