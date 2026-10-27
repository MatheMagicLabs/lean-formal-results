/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     baireSpace_iff_interior_iUnion_eq_empty
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Baire/Lemmas.lean, line 49
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
    have hd : ∀ n, Dense ((f n)ᶜ) := by
      intro n
      rw [← interior_eq_empty_iff_dense_compl]
      exact (hc n).isNowhereDense_iff.mp (hn n)
    rw [interior_eq_empty_iff_dense_compl, compl_iUnion]
    exact h.baire_property (fun n => (f n)ᶜ) (fun n => (hc n).isOpen_compl) hd
  · intro h
    refine ⟨fun f ho hd => ?_⟩
    have hnd : ∀ n, IsNowhereDense ((f n)ᶜ) := by
      intro n
      rw [(ho n).isClosed_compl.isNowhereDense_iff, interior_eq_empty_iff_dense_compl,
        compl_compl]
      exact hd n
    have := h (fun n => (f n)ᶜ) (fun n => (ho n).isClosed_compl) hnd
    rw [interior_eq_empty_iff_dense_compl, compl_iUnion] at this
    simpa using this
