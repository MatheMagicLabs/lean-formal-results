/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.dense_xor_isCyclic
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/Order/ArchimedeanDiscrete.lean, line 77
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem dense_xor_isCyclic [Nontrivial G] [DenselyOrdered G] (H : Subgroup G) :
    Xor (Dense (H : Set G)) (IsCyclic H) := by
  by_cases hd : Dense (H : Set G)
  · refine Or.inl ⟨hd, fun hc => ?_⟩
    obtain ⟨g, hg⟩ := hc.exists_generator
    have hH : (H : Set G) = Set.range (fun n : ℤ => (g : G) ^ n) := by
      ext x
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hg ⟨x, hx⟩)
        exact ⟨n, by simpa using congrArg Subtype.val hn⟩
      · rintro ⟨n, rfl⟩
        exact H.zpow_mem g.2 n
    apply not_denseRange_zpow (a := (g : G))
    show Dense (Set.range fun n : ℤ => (g : G) ^ n)
    rw [← hH]
    exact hd
  · exact Or.inr ⟨(dense_or_isCyclic H).resolve_left hd, hd⟩
