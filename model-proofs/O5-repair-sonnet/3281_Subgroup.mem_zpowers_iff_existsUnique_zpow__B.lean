/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.mem_zpowers_iff_existsUnique_zpow
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/ArchimedeanDensely.lean, line 44
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma Subgroup.mem_zpowers_iff_existsUnique_zpow {G : Type*}
    [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b : G} (ha : a ≠ 1) :
    b ∈ zpowers a ↔ ∃! k : ℤ, a ^ k = b := by
  have key : ∀ x : G, 1 < x → ∀ n : ℤ, x ^ n = 1 → n = 0 := by
    intro x hx n hn
    cases n with
    | ofNat n =>
      rw [show (Int.ofNat n) = (n : ℤ) from rfl, zpow_natCast] at hn
      by_contra hne
      have hn0 : n ≠ 0 := fun h => hne (by simp [h])
      exact (one_lt_pow' hx hn0).ne' hn
    | negSucc n =>
      rw [zpow_negSucc, inv_eq_one] at hn
      exact absurd hn (one_lt_pow' hx (Nat.succ_ne_zero n)).ne'
  have key' : ∀ n : ℤ, a ^ n = 1 → n = 0 := by
    intro n hn
    rcases lt_or_gt_of_ne ha with h | h
    · have h1 : 1 < a⁻¹ := one_lt_inv'.mpr h
      have := key a⁻¹ h1 (-n) (by rw [zpow_neg, inv_zpow, inv_inv, hn])
      omega
    · exact key a h n hn
  constructor
  · intro hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    refine ⟨k, hk, fun m hm => ?_⟩
    have hm' : a ^ m = b := hm
    have h1 : a ^ (m - k) = 1 := by
      rw [zpow_sub, hm', hk, mul_inv_cancel]
    have := key' _ h1
    omega
  · rintro ⟨k, hk, _⟩
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, hk⟩
