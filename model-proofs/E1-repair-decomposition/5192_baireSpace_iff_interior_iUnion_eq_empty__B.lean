/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     baireSpace_iff_interior_iUnion_eq_empty
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Baire/Lemmas.lean, line 49
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm B, verified in round 2 (round 0 = first attempt)
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
  classical
  constructor
  · intro h f hclosed hnowhere
    rcases h with ⟨h⟩
    have he : ∀ n, interior (f n) = ∅ := by
      intro n
      have hn : interior (closure (f n)) = ∅ := hnowhere n
      simpa only [(hclosed n).closure_eq] using hn
    first
    | exact h f hclosed he
    | exact h f hclosed hnowhere
    | have hd : ∀ n, Dense ((f n)ᶜ) := by
        intro n
        rw [dense_iff_closure_eq, closure_compl, he n, compl_empty]
      have hi : Dense ((⋃ n, f n)ᶜ) := by
        simpa only [compl_iUnion] using
          h (fun n => (f n)ᶜ) (fun n => (hclosed n).isOpen_compl) hd
      have hc := hi.closure_eq
      rw [closure_compl] at hc
      simpa only [compl_compl, compl_univ] using
        congrArg (fun s : Set X => sᶜ) hc
  · intro h
    constructor
    intro f hf hg
    first
    | exact h f hf hg
    | exact h f hf (fun n => by
        change interior (closure (f n)) = ∅
        rw [(hf n).closure_eq]
        exact hg n)
    | have he : interior (⋃ n, (f n)ᶜ) = ∅ := by
        apply h
        · intro n
          exact (hf n).isClosed_compl
        · intro n
          change interior (closure ((f n)ᶜ)) = ∅
          rw [(hf n).isClosed_compl.closure_eq, interior_compl,
            (hg n).closure_eq, compl_univ]
      have hd : Dense ((⋃ n, (f n)ᶜ)ᶜ) := by
        rw [dense_iff_closure_eq, closure_compl, he, compl_empty]
      simpa only [compl_iUnion, compl_compl] using hd
