/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     baireSpace_iff_interior_iUnion_eq_empty
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Baire/Lemmas.lean, line 49
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem baireSpace_iff_interior_iUnion_eq_empty :
    BaireSpace X ↔ ∀ f : ℕ → Set X,
      (∀ n, IsClosed (f n)) → (∀ n, IsNowhereDense (f n)) → interior (⋃ n, f n) = ∅ := by
  have key : ∀ s : Set X, IsClosed s → (IsNowhereDense s ↔ interior s = ∅) := by
    intro s hs
    first
      | exact hs.isNowhereDense_iff
      | (unfold IsNowhereDense; rw [hs.closure_eq])
  constructor
  · intro h f hc hn
    have hd : ∀ n, Dense (f n)ᶜ := fun n =>
      interior_eq_empty_iff_dense_compl.1 ((key _ (hc n)).1 (hn n))
    have := h.baire_property (fun n => (f n)ᶜ) (fun n => (hc n).isOpen_compl) hd
    rw [← compl_iUnion] at this
    exact interior_eq_empty_iff_dense_compl.2 this
  · intro h
    constructor
    intro f ho hd
    have hc : ∀ n, IsClosed (f n)ᶜ := fun n => (ho n).isClosed_compl
    have hi : ∀ n, interior (f n)ᶜ = ∅ := fun n => by
      rw [interior_eq_empty_iff_dense_compl, compl_compl]
      exact hd n
    have := h (fun n => (f n)ᶜ) hc (fun n => (key _ (hc n)).2 (hi n))
    rw [interior_eq_empty_iff_dense_compl, compl_iUnion] at this
    simpa using this
