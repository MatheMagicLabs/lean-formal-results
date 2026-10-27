/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Group.isSimpleGroup_of_isCoatom
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/QuotientGroup/Simple.lean, line 27
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

@[to_additive]
theorem Group.isSimpleGroup_of_isCoatom {G : Type*} [Group G] {M : Subgroup G} [M.Normal]
    (h : IsCoatom M) : IsSimpleGroup (G ⧸ M) := by
  obtain ⟨g, hg⟩ : ∃ g, g ∉ M := by
    by_contra hc
    push_neg at hc
    exact h.1 (eq_top_iff.mpr fun x _ => hc x)
  refine { exists_pair_ne := ⟨(g : G ⧸ M), 1, fun e => hg ((QuotientGroup.eq_one_iff g).mp e)⟩,
           eq_bot_or_eq_top_of_normal := ?_ }
  intro H _
  have hle : M ≤ H.comap (QuotientGroup.mk' M) := by
    intro x hx
    simp only [Subgroup.mem_comap, QuotientGroup.mk'_apply]
    rw [(QuotientGroup.eq_one_iff x).mpr hx]
    exact H.one_mem
  rcases h.le_iff.mp hle with h1 | h1
  · right
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have : x ∈ H.comap (QuotientGroup.mk' M) := by
      rw [h1]
      exact Subgroup.mem_top x
    exact this
  · left
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have : x ∈ H.comap (QuotientGroup.mk' M) := hy
    rw [h1] at this
    exact (Subgroup.mem_bot).mpr ((QuotientGroup.eq_one_iff x).mpr this)
