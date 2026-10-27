/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Group.isSimpleGroup_of_isCoatom
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/QuotientGroup/Simple.lean, line 27
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

@[to_additive]
theorem Group.isSimpleGroup_of_isCoatom {G : Type*} [Group G] {M : Subgroup G} [M.Normal]
    (h : IsCoatom M) : IsSimpleGroup (G ⧸ M) := by
  refine { exists_pair_ne := ?_, eq_bot_or_eq_top_of_normal := ?_ }
  · obtain ⟨g, hg⟩ : ∃ g, g ∉ M := by
      by_contra hc
      push_neg at hc
      exact h.1 (eq_top_iff.2 fun g _ => hc g)
    exact ⟨(g : G ⧸ M), 1, fun he => hg ((QuotientGroup.eq_one_iff g).1 he)⟩
  · intro N hN
    have hle : M ≤ N.comap (QuotientGroup.mk' M) := by
      intro x hx
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
      exact N.one_mem
    rcases eq_or_lt_of_le hle with h1 | h1
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
      have : x ∈ N.comap (QuotientGroup.mk' M) := hx
      rwa [← h1] at this
    · right
      have h2 := h.2 _ h1
      rw [eq_top_iff]
      intro x _
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      have : x ∈ N.comap (QuotientGroup.mk' M) := by
        rw [h2]; exact Subgroup.mem_top x
      exact this
