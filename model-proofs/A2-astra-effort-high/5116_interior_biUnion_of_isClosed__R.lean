/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     interior_biUnion_of_isClosed
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Baire/Lemmas.lean, line 160
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
variable [BaireSpace X]

theorem interior_biUnion_of_isClosed {S : Set α} {f : α → Set X} (hc : ∀ s ∈ S, IsClosed (f s))
    (hS : S.Countable) (hnd : ∀ s ∈ S, IsNowhereDense (f s)) : interior (⋃ s ∈ S, f s) = ∅ := by
  classical
  have hd : Dense (⋂ s ∈ S, (f s)ᶜ) := by
    apply dense_biInter_of_isOpen (fun s hs => (hc s hs).isOpen_compl) hS
    intro s hs
    have hn := hnd s hs
    change interior (closure (f s)) = ∅ at hn
    have hi : interior (f s) = ∅ := by
      simpa only [(hc s hs).closure_eq] using hn
    rw [dense_iff_closure_eq, closure_compl, hi, compl_empty]
  have h : closure ((⋃ s ∈ S, f s)ᶜ) = univ := by
    apply dense_iff_closure_eq.mp
    simpa only [compl_iUnion] using hd
  have h' := congrArg (fun t : Set X => tᶜ) h
  simpa only [closure_compl, compl_compl, compl_univ] using h'
