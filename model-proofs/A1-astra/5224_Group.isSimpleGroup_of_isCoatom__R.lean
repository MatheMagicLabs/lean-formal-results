/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Group.isSimpleGroup_of_isCoatom
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/QuotientGroup/Simple.lean, line 27
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

@[to_additive]
theorem Group.isSimpleGroup_of_isCoatom {G : Type*} [Group G] {M : Subgroup G} [M.Normal]
    (h : IsCoatom M) : IsSimpleGroup (G ⧸ M) := by
  classical
  have hmem (x : G) :
      (QuotientGroup.mk' M) x = 1 ↔ x ∈ M := by
    apply QuotientGroup.eq_one_iff
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ M := by
    by_contra! hn
    apply h.1
    exact top_unique (by intro g _; exact hn g)
  haveI : Nontrivial (G ⧸ M) := by
    refine ⟨⟨(QuotientGroup.mk' M) g, 1, ?_⟩⟩
    exact fun heq => hg ((hmem g).mp heq)
  constructor <;> try infer_instance
  intro N hN
  have hle : M ≤ N.comap (QuotientGroup.mk' M) := by
    intro x hx
    change (QuotientGroup.mk' M) x ∈ N
    rw [(hmem x).mpr hx]
    exact N.one_mem
  rcases eq_or_lt_of_le hle with heq | hlt
  · left
    apply le_antisymm _ bot_le
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M q
    have hx : x ∈ M := by
      rw [heq]
      exact hq
    change (QuotientGroup.mk' M) x = 1
    exact (hmem x).mpr hx
  · right
    have htop : N.comap (QuotientGroup.mk' M) = ⊤ := by
      apply h.2
      exact hlt
    apply top_unique
    intro q _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M q
    change x ∈ N.comap (QuotientGroup.mk' M)
    rw [htop]
    trivial
