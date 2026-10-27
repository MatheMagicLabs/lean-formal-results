/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     baireSpace_iff_interior_iUnion_eq_empty
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Baire/Lemmas.lean, line 49
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open scoped Topology
open Filter Set TopologicalSpace
variable {X α : Type*} {ι : Sort*}
section BaireTheorem
variable [TopologicalSpace X]

theorem baireSpace_iff_interior_iUnion_eq_empty :
    BaireSpace X ↔ ∀ f : ℕ → Set X,
      (∀ n, IsClosed (f n)) → (∀ n, IsNowhereDense (f n)) → interior (⋃ n, f n) = ∅ := by
  constructor
  · intro h f hc hn
    rw [interior_eq_empty_iff_dense_compl, compl_iUnion]
    refine h.baire_property _ (fun n => (hc n).isOpen_compl) (fun n => ?_)
    rw [← interior_eq_empty_iff_dense_compl, ← (hc n).isNowhereDense_iff]
    exact hn n
  · intro h
    refine ⟨fun f ho hd => ?_⟩
    have := h (fun n => (f n)ᶜ) (fun n => (ho n).isClosed_compl) (fun n => ?_)
    · rw [interior_eq_empty_iff_dense_compl, compl_iUnion] at this
      simpa using this
    · rw [(ho n).isClosed_compl.isNowhereDense_iff, interior_eq_empty_iff_dense_compl,
        compl_compl]
      exact hd n
