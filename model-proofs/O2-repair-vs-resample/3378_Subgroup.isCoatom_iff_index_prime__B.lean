/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.isCoatom_iff_index_prime
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/Nilpotent.lean, line 1246
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 2 (round 0 = first attempt)
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
  · intro hH
    have hn : H.Normal := by
      have hN := hH.2 _ (normalizerCondition_of_isNilpotent H hH.lt_top)
      refine ⟨fun n hn g => ?_⟩
      have hg : g ∈ normalizer (H : Set G) := by rw [hN]; exact mem_top g
      exact (mem_normalizer_iff.mp hg n).mp hn
    obtain ⟨g, hg⟩ : ∃ g, g ∉ H := by
      by_contra h
      push_neg at h
      exact hH.1 (eq_top_iff.mpr fun x _ => h x)
    have hs : IsSimpleGroup (G ⧸ H) := by
      refine @IsSimpleGroup.mk _ _ ⟨⟨1, (g : G ⧸ H), ?_⟩⟩ ?_
      · exact fun h => hg ((QuotientGroup.eq_one_iff g).mp h.symm)
      · intro N _
        have hle : H ≤ N.comap (mk' H) := fun x hx => by
          rw [mem_comap, mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
          exact N.one_mem
        rcases eq_or_lt_of_le hle with heq | hlt
        · left
          rw [eq_bot_iff]
          rintro x hx
          obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
          have : y ∈ N.comap (mk' H) := hx
          rw [← heq] at this
          exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff y).mpr this)
        · right
          have htop := hH.2 _ hlt
          rw [eq_top_iff]
          rintro x -
          obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
          have : y ∈ N.comap (mk' H) := by rw [htop]; exact mem_top y
          exact this
    show (Nat.card (G ⧸ H)).Prime
    have hcen : center (G ⧸ H) = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (G ⧸ H))).resolve_left
        (Group.IsNilpotent.center_ne_bot _)
    have hnorm : ∀ K : Subgroup (G ⧸ H), K.Normal := fun K => ⟨fun n hn x => by
      have : x ∈ center (G ⧸ H) := hcen ▸ mem_top x
      rw [← mem_center_iff.mp this n, mul_inv_cancel_right]
      exact hn⟩
    obtain ⟨g, hg⟩ := exists_ne (1 : G ⧸ H)
    have hfo : IsOfFinOrder g := by
      haveI := hnorm (Subgroup.zpowers (g ^ 2))
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers (g ^ 2)) with h | h
      · rw [isOfFinOrder_iff_zpow_eq_one]
        refine ⟨2, by norm_num, ?_⟩
        have : g ^ 2 ∈ Subgroup.zpowers (g ^ 2) := Subgroup.mem_zpowers _
        rw [h, Subgroup.mem_bot] at this
        rw [zpow_two, ← pow_two]
        exact this
      · have : g ∈ Subgroup.zpowers (g ^ 2) := by rw [h]; exact Subgroup.mem_top g
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp this
        have hk' : g ^ (2 * k) = g := by
          rw [zpow_mul, zpow_two, ← pow_two]
          exact hk
        rw [isOfFinOrder_iff_zpow_eq_one]
        refine ⟨2 * k - 1, by omega, ?_⟩
        rw [zpow_sub_one, hk', mul_inv_cancel]
    have hz : Subgroup.zpowers g = ⊤ := by
      haveI := hnorm (Subgroup.zpowers g)
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers g) with h | h
      · exact absurd (Subgroup.zpowers_eq_bot.mp h) hg
      · exact h
    have hmem : ∀ x, x ∈ Subgroup.zpowers g := fun x => by
      rw [hz]; exact Subgroup.mem_top x
    have hc : Nat.card (G ⧸ H) = orderOf g :=
      (Nat.card_congr (Equiv.subtypeUnivEquiv hmem)).symm.trans (Nat.card_zpowers g)
    haveI : Finite (G ⧸ H) :=
      Nat.finite_of_card_ne_zero (by rw [hc]; exact hfo.orderOf_pos.ne')
    first
      | exact IsSimpleGroup.prime_card
      | exact (IsSimpleGroup.prime_card (α := G ⧸ H))
  · intro hp
    show H ≠ ⊤ ∧ ∀ K, H < K → K = ⊤
    refine ⟨fun h => ?_, fun K hK => ?_⟩
    · rw [h, Subgroup.index_top] at hp
      exact Nat.not_prime_one hp
    · obtain ⟨r, hr1, hmul⟩ : ∃ r, (r = 1 → K ≤ H) ∧ r * K.index = H.index := by
        first
          | exact ⟨_, Subgroup.relIndex_eq_one.mp, Subgroup.relIndex_mul_index hK.le⟩
          | exact ⟨_, Subgroup.relindex_eq_one.mp, Subgroup.relindex_mul_index hK.le⟩
      have hd : K.index ∣ H.index := Dvd.intro_left _ hmul
      rcases hp.eq_one_or_self_of_dvd _ hd with h1 | h2
      · exact Subgroup.index_eq_one.mp h1
      · rw [h2] at hmul
        have hr : r = 1 := Nat.eq_of_mul_eq_mul_right hp.pos (hmul.trans (one_mul _).symm)
        exact absurd (lt_of_lt_of_le hK (hr1 hr)) (lt_irrefl _)
