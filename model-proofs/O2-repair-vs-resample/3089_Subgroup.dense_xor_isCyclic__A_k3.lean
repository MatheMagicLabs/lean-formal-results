/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.dense_xor_isCyclic
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/Order/ArchimedeanDiscrete.lean, line 77
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem dense_xor_isCyclic [Nontrivial G] [DenselyOrdered G] (H : Subgroup G) :
    Xor (Dense (H : Set G)) (IsCyclic H) := by
  by_cases hd : Dense (H : Set G)
  · refine Or.inl ⟨hd, ?_⟩
    rintro ⟨⟨g, hgH⟩, hg⟩
    have key : (H : Set G) = Set.range (g ^ · : ℤ → G) := by
      ext x
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := hg ⟨x, hx⟩
        refine ⟨n, ?_⟩
        have := congrArg Subtype.val hn
        simpa using this
      · rintro ⟨n, rfl⟩
        exact zpow_mem hgH n
    exact not_denseRange_zpow (show DenseRange (g ^ · : ℤ → G) by
      rw [DenseRange, ← key]; exact hd)
  · exact Or.inr ⟨(dense_or_isCyclic H).resolve_left hd, hd⟩
