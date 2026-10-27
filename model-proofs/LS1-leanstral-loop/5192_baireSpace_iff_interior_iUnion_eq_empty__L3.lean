/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     baireSpace_iff_interior_iUnion_eq_empty
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Baire/Lemmas.lean, line 49
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  LS1-leanstral-loop, arm L3, verified in round 3 (round 0 = first attempt)
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 in a fixed check-and-repair loop: L1 = 1 candidate per round, L3 = up to 3
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
  · intro hBaire
    intro f hf_closed hf_nowhere
    have h_int_empty : ∀ n, interior (f n) = ∅ := by
      intro n
      exact ((hf_closed n).isNowhereDense_iff.mp (hf_nowhere n))
    have h_open : ∀ n, IsOpen ((f n)ᶜ) := by
      intro n
      exact (hf_closed n).isOpen_compl
    have h_dense : ∀ n, Dense ((f n)ᶜ) := by
      intro n
      rw [← interior_eq_empty_iff_dense_compl]
      exact h_int_empty n
    have h_dense_inter : Dense (⋂ n, (f n)ᶜ) :=
      hBaire.baire_property (fun n => (f n)ᶜ) h_open h_dense
    rw [interior_eq_empty_iff_dense_compl]
    simpa [Set.compl_iUnion, compl_compl] using h_dense_inter
  · intro h
    refine { baire_property := ?_ }
    intro U hU_open hU_dense
    have hf_closed : ∀ n, IsClosed ((U n)ᶜ) := by
      intro n
      exact (hU_open n).isClosed_compl
    have hf_nowhere : ∀ n, IsNowhereDense ((U n)ᶜ) := by
      intro n
      have h_int_empty : interior ((U n)ᶜ) = ∅ :=
        (interior_eq_empty_iff_dense_compl.mpr (by simpa using hU_dense n))
      exact ((hU_open n).isClosed_compl.isNowhereDense_iff.mpr h_int_empty)
    have h_int_empty : interior (⋃ n, (U n)ᶜ) = ∅ :=
      h (fun n => (U n)ᶜ) hf_closed hf_nowhere
    rw [interior_eq_empty_iff_dense_compl] at h_int_empty
    simpa [Set.compl_iUnion, compl_compl] using h_int_empty
