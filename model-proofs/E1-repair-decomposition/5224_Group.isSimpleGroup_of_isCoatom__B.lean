/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Group.isSimpleGroup_of_isCoatom
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/QuotientGroup/Simple.lean, line 27
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm B, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

@[to_additive]
theorem Group.isSimpleGroup_of_isCoatom {G : Type*} [Group G] {M : Subgroup G} [M.Normal]
    (h : IsCoatom M) : IsSimpleGroup (G ⧸ M) := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ M := by
    by_contra hn
    apply h.1
    apply top_unique
    intro g _
    by_contra hg
    exact hn ⟨g, hg⟩
  let f : G →* G ⧸ M := QuotientGroup.mk' M
  have hf (x : G) : f x = 1 ↔ x ∈ M := by
    simp [f, QuotientGroup.eq_one_iff]
  haveI : Nontrivial (G ⧸ M) :=
    ⟨⟨f g, 1, fun he => hg ((hf g).mp he)⟩⟩
  constructor
  intro N hN
  let K : Subgroup G := N.comap f
  have hMK : M ≤ K := by
    intro x hx
    change f x ∈ N
    rw [(hf x).mpr hx]
    exact N.one_mem
  by_cases he : K = M
  · left
    apply le_antisymm
    · intro x hx
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective M x
      change f y = 1
      apply (hf y).mpr
      have hy : y ∈ K := hx
      rwa [he] at hy
    · exact bot_le
  · right
    have hK : K = ⊤ := h.2 K (lt_of_le_of_ne hMK (Ne.symm he))
    apply top_unique
    intro x _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective M x
    change y ∈ K
    rw [hK]
    trivial
