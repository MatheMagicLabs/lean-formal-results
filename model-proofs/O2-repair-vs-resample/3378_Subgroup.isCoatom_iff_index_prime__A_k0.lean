/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.isCoatom_iff_index_prime
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/Nilpotent.lean, line 1246
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[to_additive]
theorem isCoatom_iff_index_prime [Group.IsNilpotent G] (H : Subgroup G) :
    IsCoatom H ↔ H.index.Prime := by
  constructor
  · intro hcoat
    have hlt := normalizerCondition_of_isNilpotent H (lt_top_iff_ne_top.mpr hcoat.1)
    haveI hN : H.Normal := normalizer_eq_top_iff.mp (hcoat.2 _ hlt)
    have hsur : Function.Surjective (QuotientGroup.mk' H) := QuotientGroup.mk'_surjective H
    have hK : ∀ K : Subgroup (G ⧸ H), K = ⊥ ∨ K = ⊤ := by
      intro K
      have key := map_comap_eq_self_of_surjective hsur K
      have hHL : H ≤ K.comap (QuotientGroup.mk' H) := by
        intro h hh
        rw [mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff h).mpr hh]
        exact K.one_mem
      rcases hcoat.le_iff.mp hHL with h | h
      · right
        rw [← key, h, map_top_of_surjective _ hsur]
      · left
        rw [← key, h]
        exact (map_eq_bot_iff _).mpr (ker_mk' H).ge
    have hne : H ≠ ⊤ := hcoat.1
    obtain ⟨x, hx⟩ : ∃ x, x ∉ H := by
      by_contra! h
      exact hne (eq_top_iff.mpr fun x _ => h x)
    obtain ⟨g, hg⟩ : ∃ g : G ⧸ H, g ≠ 1 :=
      ⟨x, fun h => hx ((QuotientGroup.eq_one_iff x).mp h)⟩
    have hgtop : zpowers g = ⊤ := by
      rcases hK (zpowers g) with h | h
      · have := mem_zpowers g
        rw [h, mem_bot] at this
        exact absurd this hg
      · exact h
    have hn : orderOf g ≠ 0 := by
      intro h0
      rcases hK (zpowers (g ^ 2)) with h | h
      · have h2 : g ^ 2 = 1 := by
          have := mem_zpowers (g ^ 2)
          rw [h, mem_bot] at this
          exact this
        have := orderOf_dvd_of_pow_eq_one h2
        rw [h0] at this
        exact absurd (zero_dvd_iff.mp this) (by norm_num)
      · have hm : g ∈ zpowers (g ^ 2) := h ▸ mem_top g
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hm
        rw [pow_two] at hk
        have h1 : g ^ (2 * k - 1) = 1 := by
          rw [zpow_sub_one, zpow_mul, zpow_two, hk, mul_inv_cancel]
        have := orderOf_dvd_iff_zpow_eq_one.mpr h1
        rw [h0, Nat.cast_zero, zero_dvd_iff] at this
        omega
    have hcard : Nat.card (G ⧸ H) = orderOf g := by
      rw [← Nat.card_zpowers g, hgtop, Subgroup.card_top]
    show (Nat.card (G ⧸ H)).Prime
    rw [hcard, Nat.prime_def]
    refine ⟨?_, fun m hm => ?_⟩
    · have : orderOf g ≠ 1 := fun h => hg (orderOf_eq_one_iff.mp h)
      omega
    · have hm0 : m ≠ 0 := by
        rintro rfl
        exact hn (zero_dvd_iff.mp hm)
      rcases hK (zpowers (g ^ m)) with h | h
      · right
        have h2 : g ^ m = 1 := by
          have := mem_zpowers (g ^ m)
          rw [h, mem_bot] at this
          exact this
        exact Nat.dvd_antisymm hm (orderOf_dvd_of_pow_eq_one h2)
      · left
        have h3 := Nat.card_zpowers (g ^ m)
        rw [h, Subgroup.card_top, hcard, orderOf_pow_of_dvd hm0 hm] at h3
        have h4 := Nat.div_mul_cancel hm
        rw [← h3] at h4
        exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn) (by rw [mul_one]; exact h4)
  · intro hp
    refine ⟨fun h => ?_, fun K hK => ?_⟩
    · rw [h, index_top] at hp
      exact Nat.not_prime_one hp
    · have := relIndex_mul_index hK.le
      rw [← this] at hp
      rcases Nat.prime_mul_iff.mp hp with ⟨_, h1⟩ | ⟨_, h1⟩
      · exact index_eq_one.mp h1
      · exact absurd (relIndex_eq_one.mp h1) (not_le_of_gt hK)
