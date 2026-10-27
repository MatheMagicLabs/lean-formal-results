/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Group.isSimpleGroup_of_isCoatom
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/QuotientGroup/Simple.lean, line 27
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm N2, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

@[to_additive]
theorem Group.isSimpleGroup_of_isCoatom {G : Type*} [Group G] {M : Subgroup G} [M.Normal]
    (h : IsCoatom M) : IsSimpleGroup (G ⧸ M) := by
  rcases h with ⟨hne, hmax⟩
  let f : G →* G ⧸ M := QuotientGroup.mk' M
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective M
  have hk : f.ker = M := by
    simp [f]
  haveI : Nontrivial (G ⧸ M) := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hs
    apply hne
    apply top_unique
    intro x _
    have hx : x ∈ f.ker := by
      change f x = 1
      exact @Subsingleton.elim _ hs _ _
    rwa [hk] at hx
  constructor <;> try infer_instance
  intro H
  intros
  have hle : M ≤ H.comap f := by
    intro x hx
    have hx' : x ∈ f.ker := by
      rwa [hk]
    change f x ∈ H
    change f x = 1 at hx'
    rw [hx']
    exact H.one_mem
  by_cases he : H.comap f = M
  · left
    ext y
    obtain ⟨x, rfl⟩ := hf y
    change x ∈ H.comap f ↔ x ∈ f.ker
    rw [he, hk]
  · right
    have ht : H.comap f = ⊤ := by
      apply hmax
      exact lt_of_le_of_ne hle (Ne.symm he)
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := hf y
    change x ∈ H.comap f
    rw [ht]
    trivial
