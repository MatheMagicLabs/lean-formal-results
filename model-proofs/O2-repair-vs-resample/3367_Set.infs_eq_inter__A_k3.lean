/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Set.infs_eq_inter
Source:      Mathlib @ a02a63c2, Mathlib/Data/Set/Sups.lean, line 316
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[simp]
theorem infs_eq_inter {s t : Set α} (hs : IsLowerSet s) (ht : IsLowerSet t) : s ⊼ t = s ∩ t := by
  ext x
  simp only [mem_infs, mem_inter_iff]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨hs inf_le_left ha, ht inf_le_right hb⟩
  · rintro ⟨hxs, hxt⟩
    exact ⟨x, hxs, x, hxt, inf_idem x⟩
