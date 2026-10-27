/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Group.isSimpleGroup_of_isCoatom
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/QuotientGroup/Simple.lean, line 27
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

@[to_additive]
theorem Group.isSimpleGroup_of_isCoatom {G : Type*} [Group G] {M : Subgroup G} [M.Normal]
    (h : IsCoatom M) : IsSimpleGroup (G ⧸ M) := by
  have : Nontrivial (G ⧸ M) := by
    obtain ⟨g, hg⟩ : ∃ g, g ∉ M := by
      by_contra hc
      push_neg at hc
      exact h.1 (eq_top_iff.mpr fun x _ => hc x)
    exact ⟨⟨(g : G ⧸ M), 1, fun he => hg ((QuotientGroup.eq_one_iff g).mp he)⟩⟩
  refine ⟨?_⟩
  intro H _
  have hle : M ≤ H.comap (QuotientGroup.mk' M) := by
    intro x hx
    show (QuotientGroup.mk x : G ⧸ M) ∈ H
    rw [(QuotientGroup.eq_one_iff x).mpr hx]
    exact H.one_mem
  rcases hle.eq_or_lt with heq | hlt
  · left
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have : g ∈ H.comap (QuotientGroup.mk' M) := hx
    rw [← heq] at this
    exact (Subgroup.mem_bot).mpr ((QuotientGroup.eq_one_iff g).mpr this)
  · right
    have := h.2 _ hlt
    rw [eq_top_iff]
    intro x _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hg : g ∈ H.comap (QuotientGroup.mk' M) := by
      rw [this]; exact Subgroup.mem_top g
    exact hg
