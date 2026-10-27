/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Group.isSimpleGroup_of_isCoatom
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/QuotientGroup/Simple.lean, line 27
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

@[to_additive]
theorem Group.isSimpleGroup_of_isCoatom {G : Type*} [Group G] {M : Subgroup G} [M.Normal]
    (h : IsCoatom M) : IsSimpleGroup (G ⧸ M) := by
  classical
  have hnt : Nontrivial (G ⧸ M) := by
    by_contra hn
    haveI : Subsingleton (G ⧸ M) := not_nontrivial_iff_subsingleton.mp hn
    apply h.1
    apply top_unique
    intro g _
    have hg : QuotientGroup.mk g = (1 : G ⧸ M) := Subsingleton.elim _ _
    simpa only [QuotientGroup.eq_one_iff] using hg
  haveI := hnt
  constructor <;> first
    | exact hnt
    | intro N hN
      have hle : M ≤ N.comap (QuotientGroup.mk' M) := by
        intro g hg
        change QuotientGroup.mk g ∈ N
        have hg' : QuotientGroup.mk g = (1 : G ⧸ M) := by
          simpa only [QuotientGroup.eq_one_iff] using hg
        rw [hg']
        exact N.one_mem
      by_cases he : M = N.comap (QuotientGroup.mk' M)
      · left
        apply le_antisymm
        · intro q
          refine Quotient.inductionOn q ?_
          intro g hg
          change QuotientGroup.mk g = 1
          have hg' : g ∈ N.comap (QuotientGroup.mk' M) := hg
          rw [← he] at hg'
          simpa only [QuotientGroup.eq_one_iff] using hg'
        · exact bot_le
      · right
        have ht : N.comap (QuotientGroup.mk' M) = ⊤ := by
          apply h.2
          exact lt_of_le_of_ne hle he
        apply top_unique
        intro q _
        refine Quotient.inductionOn q ?_
        intro g
        have hg : g ∈ N.comap (QuotientGroup.mk' M) := by
          rw [ht]
          trivial
        exact hg
