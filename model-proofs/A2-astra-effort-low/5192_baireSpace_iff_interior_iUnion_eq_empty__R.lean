/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     baireSpace_iff_interior_iUnion_eq_empty
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Baire/Lemmas.lean, line 49
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 1 (round 0 = first attempt)
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

theorem baireSpace_iff_interior_iUnion_eq_empty :
    BaireSpace X ↔ ∀ f : ℕ → Set X,
      (∀ n, IsClosed (f n)) → (∀ n, IsNowhereDense (f n)) → interior (⋃ n, f n) = ∅ := by
  constructor
  · intro h f hclosed hnowhere
    letI : BaireSpace X := h
    have hd : ∀ n, Dense (f n)ᶜ := by
      intro n
      have hn := hnowhere n
      change interior (closure (f n)) = ∅ at hn
      have he : interior (f n) = ∅ := by
        simpa only [(hclosed n).closure_eq] using hn
      rw [dense_iff_closure_eq, closure_compl, he, compl_empty]
    have hi : Dense (⋂ n, (f n)ᶜ) :=
      BaireSpace.baire_property _ (fun n => (hclosed n).isOpen_compl) hd
    have hc : Dense (⋃ n, f n)ᶜ := by
      simpa only [compl_iUnion] using hi
    have he := hc.closure_eq
    rw [closure_compl] at he
    have he' := congrArg (fun s : Set X => sᶜ) he
    simpa only [compl_compl, compl_univ] using he'
  · intro h
    constructor
    intro f hopen hdense
    have hn : ∀ n, IsNowhereDense (f n)ᶜ := by
      intro n
      change interior (closure (f n)ᶜ) = ∅
      rw [(hopen n).isClosed_compl.closure_eq,
        interior_compl, (hdense n).closure_eq, compl_univ]
    have he := h (fun n => (f n)ᶜ)
      (fun n => (hopen n).isClosed_compl) hn
    rw [dense_iff_closure_eq]
    have hc : closure ((⋃ n, (f n)ᶜ)ᶜ) = univ := by
      rw [closure_compl, he, compl_empty]
    simpa only [compl_iUnion, compl_compl] using hc
