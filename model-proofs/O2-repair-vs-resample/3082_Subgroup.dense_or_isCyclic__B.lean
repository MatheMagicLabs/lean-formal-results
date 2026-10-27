/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.dense_or_isCyclic
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/Order/ArchimedeanDiscrete.lean, line 61
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 3 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem dense_or_isCyclic (H : Subgroup G) : Dense (H : Set G) ∨ IsCyclic H := by
  have key : ∀ a : G, IsCyclic (zpowers a) := by
    intro a
    refine ⟨⟨⟨a, mem_zpowers a⟩, ?_⟩⟩
    rintro ⟨x, hx⟩
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    exact mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simp)⟩
  by_cases h : ∃ a, IsLeast {g : G | g ∈ H ∧ 1 < g} a
  · obtain ⟨a, ha⟩ := h
    right
    have e := cyclic_of_min ha
    subst e
    exact key a
  · by_cases hb : H = ⊥
    · right
      subst hb
      rw [← zpowers_one_eq_bot]
      exact key 1
    · left
      exact dense_of_no_min H hb h
