/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.isCoatom_iff_index_prime
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/Nilpotent.lean, line 1246
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
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
    have hlt := normalizerCondition_of_isNilpotent H hH.lt_top
    haveI hN : H.Normal := normalizer_eq_top_iff.mp (hH.2 _ hlt)
    obtain ⟨g0, hg0⟩ : ∃ g, g ∉ H := by
      by_contra h
      push_neg at h
      exact hH.1 (eq_top_iff.mpr fun x _ => h x)
    haveI hnt : Nontrivial (G ⧸ H) :=
      ⟨⟨(g0 : G ⧸ H), 1, fun h => hg0 ((QuotientGroup.eq_one_iff g0).mp h)⟩⟩
    haveI hsimp : IsSimpleGroup (G ⧸ H) := by
      refine { toNontrivial := hnt, eq_bot_or_eq_top_of_normal := fun N _ => ?_ }
      have hle : H ≤ comap (mk' H) N := by
        intro x hx
        rw [mem_comap, mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
        exact one_mem N
      have hsur : Function.Surjective (mk' H) := QuotientGroup.mk_surjective
      have hmap : map (mk' H) (comap (mk' H) N) = N := map_comap_eq_self_of_surjective hsur N
      rcases hH.le_iff.mp hle with h | h
      · right
        rw [← hmap, h]
        exact map_top_of_surjective _ hsur
      · left
        rw [← hmap, h]
        exact (Subgroup.map_eq_bot_iff _).mpr (by rw [ker_mk'])
    have hz : ∀ x : G ⧸ H, x ≠ 1 → zpowers x = ⊤ := fun x hx =>
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers x)).resolve_left
        (by simpa using hx)
    haveI hfin : Finite (G ⧸ H) := by
      obtain ⟨g, hg⟩ := exists_ne (1 : G ⧸ H)
      have hne : orderOf g ≠ 0 := by
        intro h0
        have hnf : ¬ IsOfFinOrder g := orderOf_eq_zero_iff.mp h0
        have h2 : g ^ 2 ≠ 1 := fun h =>
          hnf (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, h⟩)
        have hmem : g ∈ zpowers (g ^ 2) := by rw [hz _ h2]; exact mem_top g
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
        apply hnf
        rw [isOfFinOrder_iff_zpow_eq_one]
        refine ⟨2 * k - 1, by omega, ?_⟩
        rw [zpow_sub, zpow_one, zpow_mul, zpow_two, ← pow_two, hk, mul_inv_cancel]
      have hcard : Nat.card (G ⧸ H) = orderOf g := by
        rw [← Nat.card_zpowers, hz g hg, Subgroup.card_top]
      exact Nat.finite_of_card_ne_zero (hcard ▸ hne)
    show (Nat.card (G ⧸ H)).Prime
    first
    | exact IsSimpleGroup.prime_card
    | exact IsSimpleGroup.prime_card (α := G ⧸ H)
  · intro hp
    refine ⟨fun h => ?_, fun K hK => ?_⟩
    · rw [h, index_top] at hp
      exact Nat.not_prime_one hp
    · have hmul : H.relIndex K * K.index = H.index := by
        first
        | exact relIndex_mul_index hK.le
        | exact relindex_mul_index hK.le
      rw [← hmul] at hp
      rcases Nat.prime_mul_iff.mp hp with ⟨_, h1⟩ | ⟨_, h1⟩
      · exact index_eq_one.mp h1
      · have hKH : K ≤ H := by
          first
          | exact relIndex_eq_one.mp h1
          | exact relindex_eq_one.mp h1
        exact absurd (lt_of_lt_of_le hK hKH) (lt_irrefl _)
