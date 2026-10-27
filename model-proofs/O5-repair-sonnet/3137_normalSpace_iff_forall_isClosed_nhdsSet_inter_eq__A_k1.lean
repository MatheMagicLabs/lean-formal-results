/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     normalSpace_iff_forall_isClosed_nhdsSet_inter_eq
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Separation/Regular.lean, line 554
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem normalSpace_iff_forall_isClosed_nhdsSet_inter_eq :
    NormalSpace X ↔ ∀ s t : Set X, IsClosed s → IsClosed t → 𝓝ˢ (s ∩ t) = 𝓝ˢ s ⊓ 𝓝ˢ t := by
  constructor
  · intro _ s t hs ht
    exact hs.nhdsSet_inter_eq ht
  · intro H
    refine ⟨fun s t hs ht hd => ?_⟩
    rw [separatedNhds_iff_disjoint, disjoint_iff, ← H s t hs ht,
      Set.disjoint_iff_inter_eq_empty.mp hd, nhdsSet_empty]
