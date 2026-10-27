/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     baireSpace_iff_interior_iUnion_eq_empty
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Baire/Lemmas.lean, line 49
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  · rintro ⟨h⟩ f hc hn
    have he : ∀ n, interior (f n) = ∅ := by
      intro n
      simpa [IsNowhereDense, dense_iff_closure_eq, closure_compl,
        (hc n).closure_eq] using hn n
    have hd : ∀ n, Dense (f n)ᶜ := by
      intro n
      rw [dense_iff_closure_eq, closure_compl, he n, compl_empty]
    have hi : Dense (⋃ n, f n)ᶜ := by
      simpa only [compl_iUnion] using
        h (fun n => (f n)ᶜ) (fun n => (hc n).isOpen_compl) hd
    rw [dense_iff_closure_eq, closure_compl] at hi
    simpa only [compl_compl, compl_univ] using
      congrArg (fun s : Set X => sᶜ) hi
  · intro h
    constructor
    intro f ho hd
    have hn : ∀ n, IsNowhereDense (f n)ᶜ := by
      intro n
      simp [IsNowhereDense, dense_iff_closure_eq,
        (ho n).isClosed_compl.closure_eq, closure_compl,
        interior_compl, (hd n).closure_eq]
    have hi := h (fun n => (f n)ᶜ)
      (fun n => (ho n).isClosed_compl) hn
    have he : (⋂ n, f n) = (⋃ n, (f n)ᶜ)ᶜ := by
      simp only [compl_iUnion, compl_compl]
    rw [dense_iff_closure_eq, he, closure_compl, hi, compl_empty]
