/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.isHamiltonian_cycleGraph_iff
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean, line 392
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  LS1-leanstral-loop, arm L3, verified in round 0 (round 0 = first attempt)
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 in a fixed check-and-repair loop: L1 = 1 candidate per round, L3 = up to 3
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
theorem isHamiltonian_cycleGraph_iff {n : ℕ} : (cycleGraph n).IsHamiltonian ↔ n = 1 ∨ 3 ≤ n := by
  refine ⟨?_, ?_⟩
  · intro h
    by_contra! hnot
    have hnot' : n ≠ 1 ∧ ¬ 3 ≤ n := by
      simpa [not_or] using hnot
    rcases hnot' with ⟨h1, h3⟩
    have h_lt_3 : n < 3 := Nat.lt_of_not_ge h3
    have h_cases : n = 0 ∨ n = 2 := by
      omega
    rcases h_cases with (rfl | rfl)
    · exact not_isHamiltonian_of_isEmpty h
    · exact not_isHamiltonian_of_card_eq_two (by simpa [Fintype.card_fin] using h) h
  · intro h
    rcases h with (rfl | h)
    · exact IsHamiltonian.of_card_eq_one (by simp)
    · exact isHamiltonian_cycleGraph h
