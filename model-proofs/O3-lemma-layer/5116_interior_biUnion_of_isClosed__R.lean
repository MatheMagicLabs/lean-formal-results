/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     interior_biUnion_of_isClosed
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Baire/Lemmas.lean, line 160
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
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
variable [BaireSpace X]

theorem interior_biUnion_of_isClosed {S : Set α} {f : α → Set X} (hc : ∀ s ∈ S, IsClosed (f s))
    (hS : S.Countable) (hnd : ∀ s ∈ S, IsNowhereDense (f s)) : interior (⋃ s ∈ S, f s) = ∅ := by
  rw [interior_eq_empty_iff_dense_compl]
  simp only [compl_iUnion]
  refine dense_biInter_of_isOpen (f := fun s => (f s)ᶜ)
    (fun s hs => (hc s hs).isOpen_compl) hS ?_
  intro s hs
  show Dense (f s)ᶜ
  rw [← interior_eq_empty_iff_dense_compl]
  have := hnd s hs
  rwa [IsNowhereDense, (hc s hs).closure_eq] at this
