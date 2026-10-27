/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.isCyclic_of_disjoint_Ioo_one
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/ArchimedeanDensely.lean, line 107
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem Subgroup.isCyclic_of_disjoint_Ioo_one {G : Type*} [CommGroup G] [LinearOrder G]
    [IsOrderedMonoid G] [MulArchimedean G] {H : Subgroup G} {a : G} (h₀ : 1 < a)
    (hd : Disjoint (H : Set G) (Ioo 1 a)) : IsCyclic H := by
  by_cases hS : ∃ s, s ∈ H ∧ 1 < s
  · obtain ⟨s, hsH, hs1⟩ := hS
    have key : ∀ n : ℕ, ∀ s ∈ H, 1 < s → s ≤ a ^ n →
        ∃ m, IsLeast {g : G | g ∈ H ∧ 1 < g} m := by
      intro n
      induction n with
      | zero =>
        intro s _ hs1 hs
        simp at hs
        exact absurd hs1 (not_lt.2 hs)
      | succ n ih =>
        intro s hsH hs1 hs
        by_cases hl : IsLeast {g : G | g ∈ H ∧ 1 < g} s
        · exact ⟨s, hl⟩
        · have hex : ∃ t ∈ H, 1 < t ∧ t < s := by
            by_contra hne
            push_neg at hne
            exact hl ⟨⟨hsH, hs1⟩, fun g hg => hne g hg.1 hg.2⟩
          obtain ⟨t, htH, ht1, hts⟩ := hex
          have hst : a ≤ s / t := by
            by_contra hlt
            push_neg at hlt
            exact Set.disjoint_left.1 hd (H.div_mem hsH htH) ⟨one_lt_div'.2 hts, hlt⟩
          refine ih t htH ht1 ?_
          have h1 : a * t ≤ s := by rwa [le_div_iff_mul_le] at hst
          have h2 : a * t ≤ a * a ^ n := by
            calc a * t ≤ s := h1
              _ ≤ a ^ (n + 1) := hs
              _ = a * a ^ n := pow_succ' a n
          exact le_of_mul_le_mul_left' h2
    obtain ⟨n, hn⟩ := MulArchimedean.arch s h₀
    obtain ⟨m, hm⟩ := key n s hsH hs1 hn
    have := Subgroup.cyclic_of_min hm
    rw [← this]
    infer_instance
  · push_neg at hS
    have hbot : H = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro g hg
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact absurd (hS _ (H.inv_mem hg)) (not_le.2 (one_lt_inv'.2 h))
      · exact absurd (hS g hg) (not_le.2 h)
    rw [hbot]
    infer_instance
