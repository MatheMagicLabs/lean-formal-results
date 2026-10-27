/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Set.infs_eq_inter
Source:      Mathlib @ a02a63c2, Mathlib/Data/Set/Sups.lean, line 316
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[simp]
theorem infs_eq_inter {s t : Set α} (hs : IsLowerSet s) (ht : IsLowerSet t) : s ⊼ t = s ∩ t := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_infs.1 hx
    exact ⟨hs inf_le_left ha, ht inf_le_right hb⟩
  · intro x hx
    exact mem_infs.2 ⟨x, hx.1, x, hx.2, inf_idem _⟩
