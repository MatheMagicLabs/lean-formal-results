/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Group.isSimpleGroup_of_isCoatom
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/QuotientGroup/Simple.lean, line 27
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

@[to_additive]
theorem Group.isSimpleGroup_of_isCoatom {G : Type*} [Group G] {M : Subgroup G} [M.Normal]
    (h : IsCoatom M) : IsSimpleGroup (G ⧸ M) := by
  classical
  let f : G →* G ⧸ M := QuotientGroup.mk' M
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective M
  haveI : Nontrivial (G ⧸ M) := by
    obtain ⟨g, hg⟩ : ∃ g : G, g ∉ M := by
      by_contra hn
      apply h.1
      apply top_unique
      intro g _
      by_contra hg
      exact hn ⟨g, hg⟩
    refine ⟨⟨f g, 1, ?_⟩⟩
    intro he
    change (QuotientGroup.mk g : G ⧸ M) = 1 at he
    exact hg (by simpa only [QuotientGroup.eq_one_iff] using he)
  apply IsSimpleGroup.mk
  all_goals try infer_instance
  intro H hH
  have hle : M ≤ H.comap f := by
    intro g hg
    change f g ∈ H
    have he : f g = 1 := by
      change (QuotientGroup.mk g : G ⧸ M) = 1
      simpa only [QuotientGroup.eq_one_iff] using hg
    rw [he]
    exact H.one_mem
  rcases eq_or_lt_of_le hle with he | hlt
  · left
    apply le_antisymm ?_ bot_le
    intro q hq
    obtain ⟨g, rfl⟩ := hf q
    have hg : g ∈ H.comap f := hq
    rw [← he] at hg
    change (QuotientGroup.mk g : G ⧸ M) = 1
    simpa only [QuotientGroup.eq_one_iff] using hg
  · right
    have ht : H.comap f = ⊤ := by
      apply h.2
      exact hlt
    apply top_unique
    intro q _
    obtain ⟨g, rfl⟩ := hf q
    have hg : g ∈ H.comap f := by
      rw [ht]
      exact Subgroup.mem_top g
    exact hg
