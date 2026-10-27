/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     baireSpace_iff_interior_iUnion_eq_empty
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Baire/Lemmas.lean, line 49
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
  · intro h f hclosed hnowhere
    rcases h with ⟨h⟩
    have hd : ∀ n, Dense (f n)ᶜ := by
      intro n
      have hn := hnowhere n
      change interior (closure (f n)) = ∅ at hn
      rw [(hclosed n).closure_eq] at hn
      rw [dense_iff_closure_eq, closure_compl, hn, compl_empty]
    have hi : Dense ((⋃ n, f n)ᶜ) := by
      simpa only [compl_iUnion] using
        h (fun n => (f n)ᶜ) (fun n => (hclosed n).isOpen_compl) hd
    simpa only [closure_compl, compl_compl, compl_univ] using
      congrArg (fun s : Set X => sᶜ) hi.closure_eq
  · intro h
    constructor
    intro f hopen hdense
    have he : interior (⋃ n, (f n)ᶜ) = ∅ := by
      apply h
      · intro n
        exact (hopen n).isClosed_compl
      · intro n
        change interior (closure (f n)ᶜ) = ∅
        rw [(hopen n).isClosed_compl.closure_eq, interior_compl,
          (hdense n).closure_eq, compl_univ]
    have hd : Dense ((⋃ n, (f n)ᶜ)ᶜ) := by
      rw [dense_iff_closure_eq, closure_compl, he, compl_empty]
    simpa only [compl_iUnion, compl_compl] using hd
