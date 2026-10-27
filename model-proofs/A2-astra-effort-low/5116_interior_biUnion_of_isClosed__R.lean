/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     interior_biUnion_of_isClosed
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Baire/Lemmas.lean, line 160
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
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
  letI : Countable S := hS.to_subtype
  letI : Encodable S := Encodable.ofCountable S
  have hd : ∀ s : S, Dense (f s)ᶜ := by
    intro s
    have hn := hnd s s.property
    change interior (closure (f s)) = ∅ at hn
    rw [(hc s s.property).closure_eq] at hn
    rw [dense_iff_closure_eq, closure_compl, hn, compl_empty]
  let g : ℕ → Set X := fun n =>
    match (Encodable.decode n : Option S) with
    | none => univ
    | some s => (f s)ᶜ
  have ho : ∀ n, IsOpen (g n) := by
    intro n
    cases he : (Encodable.decode n : Option S) with
    | none => simpa [g, he] using isOpen_univ (X := X)
    | some s => simpa [g, he] using (hc s s.property).isOpen_compl
  have hg : ∀ n, Dense (g n) := by
    intro n
    cases he : (Encodable.decode n : Option S) with
    | none => simp [g, he]
    | some s => simpa [g, he] using hd s
  have hi : Dense (⋂ n, g n) :=
    BaireSpace.baire_property g ho hg
  have h : Dense ((⋃ s ∈ S, f s)ᶜ) := hi.mono (by
    intro x hx
    simp only [mem_compl_iff, mem_iUnion, not_exists]
    intro s hs
    have hn := mem_iInter.mp hx (Encodable.encode (⟨s, hs⟩ : S))
    simpa [g, Encodable.encodek] using hn)
  have he := h.closure_eq
  rw [closure_compl] at he
  apply compl_injective
  simpa only [compl_empty] using he
