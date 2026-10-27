/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     baireSpace_iff_interior_iUnion_eq_empty
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Baire/Lemmas.lean, line 49
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 1 (round 0 = first attempt)
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
    rcases h with ⟨h⟩
    have hi : ∀ n, interior (f n) = ∅ := by
      intro n
      have hn' := hn n
      change interior (closure (f n)) = ∅ at hn'
      simpa only [(hc n).closure_eq] using hn'
    have hd : Dense (⋂ n, (f n)ᶜ) :=
      h (fun n => (f n)ᶜ)
        (fun n => (hc n).isOpen_compl)
        (fun n => by
          rw [dense_iff_closure_eq, closure_compl, hi n, compl_empty])
    have he : interior ((⋂ n, (f n)ᶜ)ᶜ) = ∅ := by
      rw [interior_compl, hd.closure_eq, compl_univ]
    simpa only [compl_iInter, compl_compl] using he
  · intro h
    constructor
    intro f ho hd
    have hc : ∀ n, IsClosed ((f n)ᶜ) :=
      fun n => (ho n).isClosed_compl
    have hn : ∀ n, IsNowhereDense ((f n)ᶜ) := by
      intro n
      change interior (closure ((f n)ᶜ)) = ∅
      rw [(hc n).closure_eq, interior_compl, (hd n).closure_eq, compl_univ]
    have he : interior ((⋂ n, f n)ᶜ) = ∅ := by
      simpa only [compl_iInter] using h (fun n => (f n)ᶜ) hc hn
    rw [interior_compl] at he
    rw [dense_iff_closure_eq]
    apply compl_injective
    simpa only [compl_univ] using he
