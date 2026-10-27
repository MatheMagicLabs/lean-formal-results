/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     baireSpace_iff_interior_iUnion_eq_empty
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Baire/Lemmas.lean, line 49
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem baireSpace_iff_interior_iUnion_eq_empty :
    BaireSpace X ↔ ∀ f : ℕ → Set X,
      (∀ n, IsClosed (f n)) → (∀ n, IsNowhereDense (f n)) → interior (⋃ n, f n) = ∅ := by
  refine ⟨fun hB f hc hn => ?_, fun h => ⟨fun f ho hd => ?_⟩⟩
  · rw [interior_eq_empty_iff_dense_compl, compl_iUnion]
    refine hB.baire_property _ (fun n => (hc n).isOpen_compl) (fun n => ?_)
    rw [← interior_eq_empty_iff_dense_compl]
    exact ((hc n).isNowhereDense_iff).1 (hn n)
  · have key := h (fun n => (f n)ᶜ) (fun n => (ho n).isClosed_compl) (fun n =>
      ((ho n).isClosed_compl.isNowhereDense_iff).2
        ((interior_eq_empty_iff_dense_compl).2 (by rw [compl_compl]; exact hd n)))
    rw [interior_eq_empty_iff_dense_compl, compl_iUnion] at key
    simpa using key
