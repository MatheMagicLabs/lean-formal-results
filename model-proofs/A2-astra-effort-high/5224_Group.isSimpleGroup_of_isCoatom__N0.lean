/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Group.isSimpleGroup_of_isCoatom
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/QuotientGroup/Simple.lean, line 27
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm N0, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

@[to_additive]
theorem Group.isSimpleGroup_of_isCoatom {G : Type*} [Group G] {M : Subgroup G} [M.Normal]
    (h : IsCoatom M) : IsSimpleGroup (G ⧸ M) := by
  classical
  haveI : Nontrivial (G ⧸ M) := by
    obtain ⟨x, hx⟩ : ∃ x : G, x ∉ M := by
      by_contra hn
      apply h.1
      ext x
      simp only [Subgroup.mem_top, iff_true]
      by_contra hx
      exact hn ⟨x, hx⟩
    refine ⟨⟨(QuotientGroup.mk' M) x, 1, ?_⟩⟩
    simpa using hx
  constructor
  all_goals
    first
    | infer_instance
    | intro K hK
      have hle : M ≤ K.comap (QuotientGroup.mk' M) := by
        intro x hx
        change (QuotientGroup.mk' M) x ∈ K
        have hx' : (QuotientGroup.mk' M) x = 1 := by
          simpa using hx
        rw [hx']
        exact K.one_mem
      have heq :
          K.comap (QuotientGroup.mk' M) = M ∨
            K.comap (QuotientGroup.mk' M) = ⊤ := by
        by_cases he : K.comap (QuotientGroup.mk' M) = M
        · exact Or.inl he
        · right
          apply h.2
          exact lt_of_le_of_ne hle (Ne.symm he)
      rcases heq with he | he
      · left
        apply le_antisymm ?_ bot_le
        intro q hq
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M q
        have hx : x ∈ M := by
          rw [← he]
          exact hq
        simpa using hx
      · right
        apply top_unique
        intro q _
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M q
        have hx : x ∈ K.comap (QuotientGroup.mk' M) := by
          rw [he]
          trivial
        exact hx
