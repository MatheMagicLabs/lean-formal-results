/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     baireSpace_iff_interior_iUnion_eq_empty
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Baire/Lemmas.lean, line 49
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem baireSpace_iff_interior_iUnion_eq_empty :
    BaireSpace X ↔ ∀ f : ℕ → Set X,
      (∀ n, IsClosed (f n)) → (∀ n, IsNowhereDense (f n)) → interior (⋃ n, f n) = ∅ := by
  refine ⟨fun h f hc hn => ?_, fun h => ⟨fun f ho hd => ?_⟩⟩
  · have hi : ∀ n, interior (f n) = ∅ := fun n => by
      have := hn n
      simpa [IsNowhereDense, (hc n).closure_eq] using this
    rw [interior_eq_empty_iff_dense_compl, compl_iUnion]
    exact h.baire_property _ (fun n => (hc n).isOpen_compl)
      (fun n => interior_eq_empty_iff_dense_compl.1 (hi n))
  · have hi : ∀ n, interior (f n)ᶜ = ∅ := fun n =>
      interior_eq_empty_iff_dense_compl.2 (by rw [compl_compl]; exact hd n)
    have := h (fun n => (f n)ᶜ) (fun n => (ho n).isClosed_compl)
      (fun n => by simpa [IsNowhereDense, (ho n).isClosed_compl.closure_eq] using hi n)
    rw [interior_eq_empty_iff_dense_compl, compl_iUnion] at this
    simpa using this
