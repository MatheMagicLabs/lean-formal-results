/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.isHamiltonian_top_iff
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean, line 404
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Finset Function
namespace SimpleGraph
variable {α : Type*} [DecidableEq α] {G : SimpleGraph α}
variable {β : Type*} [DecidableEq β] {H : SimpleGraph β}
variable {a b v : α} {p : G.Walk a b} {f : G →g H}
namespace Walk
section
variable [Fintype α]
end
variable {p : G.Walk a a}
end Walk
variable [Fintype α]

@[simp]
theorem isHamiltonian_top_iff :
    (completeGraph α).IsHamiltonian ↔ Fintype.card α = 1 ∨ 3 ≤ Fintype.card α := by
  refine ⟨fun h ↦ ?_, (·.elim .of_card_eq_one isHamiltonian_top)⟩
  contrapose h
  rcases show Fintype.card α = 0 ∨ Fintype.card α = 2 by omega with h | h
  · rw [Fintype.card_eq_zero_iff] at h
    exact not_isHamiltonian_of_isEmpty
  · exact not_isHamiltonian_of_card_eq_two h
