/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Group.isSimpleGroup_of_isCoatom
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/QuotientGroup/Simple.lean, line 27
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

@[to_additive]
theorem Group.isSimpleGroup_of_isCoatom {G : Type*} [Group G] {M : Subgroup G} [M.Normal]
    (h : IsCoatom M) : IsSimpleGroup (G ⧸ M) := by
  classical
  let f : G →* G ⧸ M := QuotientGroup.mk' M
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective M
  have hker : f.ker = M := QuotientGroup.ker_mk' M
  have hn : Nontrivial (G ⧸ M) := by
    have hex : ∃ g : G, g ∉ M := by
      by_contra! hall
      exact h.1 (top_unique (by intro g _; exact hall g))
    obtain ⟨g, hg⟩ := hex
    refine ⟨⟨f g, 1, ?_⟩⟩
    intro he
    have hg' : g ∈ f.ker := he
    exact hg (hker ▸ hg')
  have hall : ∀ K : Subgroup (G ⧸ M), K = ⊥ ∨ K = ⊤ := by
    intro K
    have hle : M ≤ K.comap f := by
      intro g hg
      have hg' : g ∈ f.ker := hker.symm ▸ hg
      change f g ∈ K
      rw [show f g = 1 from hg']
      exact K.one_mem
    rcases eq_or_lt_of_le hle with he | he
    · left
      apply le_antisymm _ bot_le
      intro x hx
      obtain ⟨g, rfl⟩ := hf x
      have hg : g ∈ M := by
        rw [he]
        exact hx
      have hg' : g ∈ f.ker := hker.symm ▸ hg
      exact Subgroup.mem_bot.mpr hg'
    · right
      have ht : K.comap f = ⊤ := h.2 (K.comap f) he
      apply top_unique
      intro x _
      obtain ⟨g, rfl⟩ := hf x
      have hg : g ∈ K.comap f := by
        rw [ht]
        trivial
      exact hg
  letI := hn
  constructor <;> intros <;> first | exact hn | exact hall _
