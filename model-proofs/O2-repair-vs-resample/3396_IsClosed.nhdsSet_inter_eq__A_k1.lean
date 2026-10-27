/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsClosed.nhdsSet_inter_eq
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Separation/Regular.lean, line 543
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem IsClosed.nhdsSet_inter_eq [NormalSpace X] {s t : Set X} (hs : IsClosed s)
    (ht : IsClosed t) : 𝓝ˢ (s ∩ t) = 𝓝ˢ s ⊓ 𝓝ˢ t := by
  refine le_antisymm (le_inf (nhdsSet_mono inter_subset_left)
    (nhdsSet_mono inter_subset_right)) ?_
  intro u hu
  obtain ⟨U, hUo, hstU, hUu⟩ := mem_nhdsSet_iff_exists.mp hu
  have hd : Disjoint (s ∩ Uᶜ) (t ∩ Uᶜ) := by
    rw [Set.disjoint_left]
    rintro x ⟨hxs, hxU⟩ ⟨hxt, -⟩
    exact hxU (hstU ⟨hxs, hxt⟩)
  obtain ⟨V, W, hV, hW, hsV, htW, hVW⟩ :=
    normal_separation (hs.inter hUo.isClosed_compl) (ht.inter hUo.isClosed_compl) hd
  refine mem_of_superset (inter_mem_inf (s := U ∪ V) (t := U ∪ W) ?_ ?_) ?_
  · refine (hUo.union hV).mem_nhdsSet.2 fun x hx => ?_
    by_cases h : x ∈ U
    · exact Or.inl h
    · exact Or.inr (hsV ⟨hx, h⟩)
  · refine (hUo.union hW).mem_nhdsSet.2 fun x hx => ?_
    by_cases h : x ∈ U
    · exact Or.inl h
    · exact Or.inr (htW ⟨hx, h⟩)
  · rintro x ⟨hx1 | hx1, hx2 | hx2⟩
    · exact hUu hx1
    · exact hUu hx1
    · exact hUu hx2
    · exact (hVW.le_bot ⟨hx1, hx2⟩).elim
