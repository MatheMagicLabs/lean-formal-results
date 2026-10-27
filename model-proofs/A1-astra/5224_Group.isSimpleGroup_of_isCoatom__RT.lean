/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Group.isSimpleGroup_of_isCoatom
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/QuotientGroup/Simple.lean, line 27
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

@[to_additive]
theorem Group.isSimpleGroup_of_isCoatom {G : Type*} [Group G] {M : Subgroup G} [M.Normal]
    (h : IsCoatom M) : IsSimpleGroup (G ⧸ M) := by
  letI : Nontrivial (G ⧸ M) := QuotientGroup.nontrivial_iff.mpr h.1
  refine ⟨fun H _ => ?_⟩
  by_cases hH : H.comap (QuotientGroup.mk' M) = M
  · left
    apply Subgroup.comap_injective (QuotientGroup.mk'_surjective M)
    calc
      H.comap (QuotientGroup.mk' M) = M := hH
      _ = (⊥ : Subgroup (G ⧸ M)).comap (QuotientGroup.mk' M) := by
        ext x
        change x ∈ M ↔ (x : G ⧸ M) = 1
        exact (QuotientGroup.eq_one_iff x).symm
  · right
    apply Subgroup.comap_injective (QuotientGroup.mk'_surjective M)
    rw [Subgroup.comap_top]
    exact h.2 _ (lt_of_le_of_ne (QuotientGroup.le_comap_mk' M H) (Ne.symm hH))
