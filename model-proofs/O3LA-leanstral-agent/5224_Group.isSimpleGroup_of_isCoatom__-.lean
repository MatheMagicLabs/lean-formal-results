/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Group.isSimpleGroup_of_isCoatom
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/QuotientGroup/Simple.lean, line 27
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA-leanstral-agent, arm -, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 as a tool-using agent (Mistral Vibe)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

@[to_additive]
theorem Group.isSimpleGroup_of_isCoatom {G : Type*} [Group G] {M : Subgroup G} [M.Normal]
    (h : IsCoatom M) : IsSimpleGroup (G ⧸ M) := by
  have h_nontriv : Nontrivial (G ⧸ M) := by
    rw [QuotientGroup.nontrivial_iff]
    exact h.1
  refine {
    exists_pair_ne := h_nontriv.exists_pair_ne,
    eq_bot_or_eq_top_of_normal := ?_
  }
  · intro K hK_normal
    have hM_le : M ≤ Subgroup.comap (QuotientGroup.mk' M) K := QuotientGroup.le_comap_mk' M K
    have h_coatom_ge := (isCoatom_iff_ge_of_le.mp h).2
    by_cases hK'_top : Subgroup.comap (QuotientGroup.mk' M) K = ⊤
    · right
      calc
        K = Subgroup.map (QuotientGroup.mk' M) (Subgroup.comap (QuotientGroup.mk' M) K) := by
          symm; exact Subgroup.map_comap_eq_self_of_surjective
            (QuotientGroup.mk'_surjective M) K
        _ = Subgroup.map (QuotientGroup.mk' M) ⊤ := by rw [hK'_top]
        _ = ⊤ := by
          rw [Subgroup.map_top, QuotientGroup.range_mk']
    · left
      have hK'_le_M : Subgroup.comap (QuotientGroup.mk' M) K ≤ M :=
        h_coatom_ge (Subgroup.comap (QuotientGroup.mk' M) K) hK'_top hM_le
      have hK'_eq_M : Subgroup.comap (QuotientGroup.mk' M) K = M :=
        le_antisymm hK'_le_M hM_le
      calc
        K = Subgroup.map (QuotientGroup.mk' M) (Subgroup.comap (QuotientGroup.mk' M) K) := by
          symm; exact Subgroup.map_comap_eq_self_of_surjective
            (QuotientGroup.mk'_surjective M) K
        _ = Subgroup.map (QuotientGroup.mk' M) M := by rw [hK'_eq_M]
        _ = ⊥ := QuotientGroup.map_mk'_self M
