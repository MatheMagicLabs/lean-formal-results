/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     baireSpace_iff_interior_iUnion_eq_empty
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Baire/Lemmas.lean, line 49
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm N0, verified in round 0 (round 0 = first attempt)
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
  · intro h f hc hn
    letI : BaireSpace X := h
    have hi : ∀ n, interior (f n) = ∅ := by
      intro n
      have hn' := hn n
      change interior (closure (f n)) = ∅ at hn'
      simpa only [(hc n).closure_eq] using hn'
    have hd : Dense (⋂ n, (f n)ᶜ) := by
      apply BaireSpace.baire_property
      · intro n
        exact (hc n).isOpen_compl
      · intro n
        rw [dense_iff_closure_eq, closure_compl, hi n, compl_empty]
    have he : closure (⋂ n, (f n)ᶜ) = univ :=
      dense_iff_closure_eq.mp hd
    rw [← compl_iUnion, closure_compl] at he
    simpa only [compl_compl, compl_univ] using
      congrArg (fun s : Set X => sᶜ) he
  · intro h
    constructor
    intro f ho hd
    have hi : ∀ n, interior ((f n)ᶜ) = ∅ := by
      intro n
      rw [interior_compl, dense_iff_closure_eq.mp (hd n), compl_univ]
    have he : interior (⋃ n, (f n)ᶜ) = ∅ := by
      apply h (fun n => (f n)ᶜ)
      · intro n
        exact (ho n).isClosed_compl
      · intro n
        change interior (closure ((f n)ᶜ)) = ∅
        rw [((ho n).isClosed_compl).closure_eq]
        exact hi n
    have hd' : Dense ((⋃ n, (f n)ᶜ)ᶜ) := by
      rw [dense_iff_closure_eq, closure_compl, he, compl_empty]
    simpa only [compl_iUnion, compl_compl] using hd'
