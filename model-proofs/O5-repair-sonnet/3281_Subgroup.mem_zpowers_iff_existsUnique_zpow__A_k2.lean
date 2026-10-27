/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.mem_zpowers_iff_existsUnique_zpow
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/ArchimedeanDensely.lean, line 44
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
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
    have h1 : a ^ (k - m) = 1 := by rw [zpow_sub, h, mul_inv_cancel]
    by_contra hne
    have hne' : k - m ≠ 0 := sub_ne_zero.mpr hne
    obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg (k - m)
    · have hn0 : n ≠ 0 := by
        rintro rfl
        apply hne'
        simpa using hn
      rw [hn, zpow_natCast] at h1
      apply ha
      first
        | exact (pow_eq_one_iff hn0).1 h1
        | exact (pow_eq_one_iff_of_ne_zero hn0).1 h1
        | exact pow_left_injective hn0 (by simpa using h1)
    · have hn0 : n ≠ 0 := by
        rintro rfl
        apply hne'
        simpa using hn
      rw [hn, zpow_neg, zpow_natCast, inv_eq_one] at h1
      apply ha
      first
        | exact (pow_eq_one_iff hn0).1 h1
        | exact (pow_eq_one_iff_of_ne_zero hn0).1 h1
        | exact pow_left_injective hn0 (by simpa using h1)
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl, fun m hm => inj m k hm⟩
  · rintro ⟨k, hk, -⟩
    exact ⟨k, hk⟩
