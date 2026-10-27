/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsClosed.nhdsSet_inter_eq
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Separation/Regular.lean, line 543
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
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
  intro U hU
  obtain ⟨O, hO, hsto, hOU⟩ := mem_nhdsSet_iff_exists.mp hU
  have hd : Disjoint (s ∩ Oᶜ) (t ∩ Oᶜ) := by
    rw [Set.disjoint_left]
    rintro x ⟨hxs, hxO⟩ ⟨hxt, -⟩
    exact hxO (hsto ⟨hxs, hxt⟩)
  obtain ⟨V, W, hV, hW, hsV, htW, hVW⟩ :=
    normal_separation (hs.inter hO.isClosed_compl) (ht.inter hO.isClosed_compl) hd
  have h1 : O ∪ V ∈ 𝓝ˢ s := by
    refine (hO.union hV).mem_nhdsSet.2 (fun x hx => ?_)
    by_cases h : x ∈ O
    · exact Or.inl h
    · exact Or.inr (hsV ⟨hx, h⟩)
  have h2 : O ∪ W ∈ 𝓝ˢ t := by
    refine (hO.union hW).mem_nhdsSet.2 (fun x hx => ?_)
    by_cases h : x ∈ O
    · exact Or.inl h
    · exact Or.inr (htW ⟨hx, h⟩)
  refine mem_of_superset (inter_mem_inf h1 h2) ?_
  rintro x ⟨hx1 | hx1, hx2 | hx2⟩
  · exact hOU hx1
  · exact hOU hx1
  · exact hOU hx2
  · exact absurd hx2 (Set.disjoint_left.mp hVW hx1)
