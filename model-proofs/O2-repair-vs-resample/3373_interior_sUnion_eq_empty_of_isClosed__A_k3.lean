/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     interior_sUnion_eq_empty_of_isClosed
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Baire/Lemmas.lean, line 147
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem interior_sUnion_eq_empty_of_isClosed {S : Set (Set X)} (hc : ∀ s ∈ S, IsClosed s)
    (hS : S.Countable) (hnd : ∀ s ∈ S, IsNowhereDense s) : interior (⋃₀ S) = ∅ := by
  rcases S.eq_empty_or_nonempty with h | h
  · simp [h]
  · rcases hS.exists_eq_range h with ⟨f, rfl⟩
    rw [sUnion_range]
    exact interior_iUnion_eq_empty_of_isClosed_nat (forall_mem_range.1 hc)
      (forall_mem_range.1 hnd)
