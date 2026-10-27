/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     baireSpace_iff_interior_iUnion_eq_empty
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Baire/Lemmas.lean, line 49
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem baireSpace_iff_interior_iUnion_eq_empty :
    BaireSpace X ↔ ∀ f : ℕ → Set X,
      (∀ n, IsClosed (f n)) → (∀ n, IsNowhereDense (f n)) → interior (⋃ n, f n) = ∅ := by
  constructor
  · intro h f hc hn
    have key : ∀ n, Dense (f n)ᶜ := fun n => by
      have := hn n
      rw [IsNowhereDense, (hc n).closure_eq] at this
      exact interior_eq_empty_iff_dense_compl.mp this
    have := h.baire_property (fun n => (f n)ᶜ) (fun n => (hc n).isOpen_compl) key
    simp only [← compl_iUnion] at this
    exact interior_eq_empty_iff_dense_compl.mpr this
  · intro h
    refine ⟨fun f ho hd => ?_⟩
    have := h (fun n => (f n)ᶜ) (fun n => (ho n).isClosed_compl) (fun n => by
      show interior (closure (f n)ᶜ) = ∅
      rw [(ho n).isClosed_compl.closure_eq, interior_eq_empty_iff_dense_compl, compl_compl]
      exact hd n)
    rw [interior_eq_empty_iff_dense_compl] at this
    simpa only [compl_iUnion, compl_compl] using this
