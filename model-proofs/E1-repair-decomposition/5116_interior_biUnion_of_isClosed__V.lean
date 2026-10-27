/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     interior_biUnion_of_isClosed
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Baire/Lemmas.lean, line 160
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 2 (round 0 = first attempt)
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
variable [BaireSpace X]

theorem interior_biUnion_of_isClosed {S : Set α} {f : α → Set X} (hc : ∀ s ∈ S, IsClosed (f s))
    (hS : S.Countable) (hnd : ∀ s ∈ S, IsNowhereDense (f s)) : interior (⋃ s ∈ S, f s) = ∅ := by
  have hd : Dense ((⋃ s ∈ S, f s)ᶜ) := by
    simp only [compl_iUnion]
    apply dense_biInter_of_isOpen (fun s hs => (hc s hs).isOpen_compl) hS
    intro s hs
    have h := hnd s hs
    change interior (closure (f s)) = ∅ at h
    rw [(hc s hs).closure_eq] at h
    rw [dense_iff_closure_eq, closure_compl, h, compl_empty]
  have h : (interior (⋃ s ∈ S, f s))ᶜ = univ := by
    simpa only [closure_compl] using hd.closure_eq
  have h' := congrArg (fun t : Set X => tᶜ) h
  simpa only [compl_compl, compl_univ] using h'
