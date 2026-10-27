/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     baireSpace_iff_interior_iUnion_eq_empty
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Baire/Lemmas.lean, line 49
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm N2, verified in round 0 (round 0 = first attempt)
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
  · rintro ⟨h⟩ f hc hn
    have hd : Dense (⋂ n, (f n)ᶜ) := by
      apply h
      · intro n
        exact (hc n).isOpen_compl
      · intro n
        have he := hn n
        change interior (closure (f n)) = ∅ at he
        rw [(hc n).closure_eq] at he
        rw [dense_iff_closure_eq, closure_compl, he]
        simp
    have he : closure ((⋃ n, f n)ᶜ) = univ := by
      simpa only [compl_iUnion] using hd.closure_eq
    have he' := congrArg (fun s : Set X => sᶜ) he
    simpa only [closure_compl, compl_compl, compl_univ] using he'
  · intro h
    constructor
    intro f ho hd
    have hc : ∀ n, IsClosed ((f n)ᶜ) :=
      fun n => (ho n).isClosed_compl
    have hn : ∀ n, IsNowhereDense ((f n)ᶜ) := by
      intro n
      change interior (closure ((f n)ᶜ)) = ∅
      rw [(hc n).closure_eq, interior_compl, (hd n).closure_eq]
      simp
    have he : interior ((⋂ n, f n)ᶜ) = ∅ := by
      simpa only [compl_iInter] using h (fun n => (f n)ᶜ) hc hn
    rw [dense_iff_closure_eq]
    have he' := congrArg (fun s : Set X => sᶜ) he
    simpa only [interior_compl, compl_compl, compl_empty] using he'
