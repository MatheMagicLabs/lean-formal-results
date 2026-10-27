/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     isMeagre_iff_eq_countable_union_isNowhereDense
Source:      Mathlib @ a02a63c2, Mathlib/Topology/GDelta/Basic.lean, line 339
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem isMeagre_iff_eq_countable_union_isNowhereDense {s : Set X} :
    IsMeagre s ↔ ∃ S : Set (Set X), (∀ t ∈ S, IsNowhereDense t) ∧ S.Countable ∧ s = ⋃₀ S := by
  rw [isMeagre_iff_countable_union_isNowhereDense]
  constructor
  · rintro ⟨S, hS, hc, hsub⟩
    refine ⟨(fun t => t ∩ s) '' S, ?_, hc.image _, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact IsNowhereDense.mono inter_subset_left (hS t ht)
    · apply Subset.antisymm
      · intro x hx
        obtain ⟨t, ht, hxt⟩ := mem_sUnion.mp (hsub hx)
        exact mem_sUnion.mpr ⟨t ∩ s, ⟨t, ht, rfl⟩, hxt, hx⟩
      · rintro x ⟨_, ⟨t, ht, rfl⟩, hxt⟩
        exact hxt.2
  · rintro ⟨S, hS, hc, rfl⟩
    exact ⟨S, hS, hc, subset_rfl⟩
