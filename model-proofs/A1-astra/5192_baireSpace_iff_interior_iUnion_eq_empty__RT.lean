/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     baireSpace_iff_interior_iUnion_eq_empty
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Baire/Lemmas.lean, line 49
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  · intro h f hf hn
    letI : BaireSpace X := h
    apply interior_eq_empty_iff_dense_compl.mpr
    rw [compl_iUnion]
    exact BaireSpace.baire_property (fun n => (f n)ᶜ)
      (fun n => (hf n).isOpen_compl)
      (fun n => (isClosed_isNowhereDense_iff_compl.mp ⟨hf n, hn n⟩).2)
  · intro h
    constructor
    intro f hf hd
    have hn : ∀ n, IsClosed (f n)ᶜ ∧ IsNowhereDense (f n)ᶜ :=
      fun n => isClosed_compl_and_isNowhereDense_compl.mpr ⟨hf n, hd n⟩
    have he := h (fun n => (f n)ᶜ) (fun n => (hn n).1) (fun n => (hn n).2)
    simpa only [compl_iUnion, compl_compl] using
      interior_eq_empty_iff_dense_compl.mp he
