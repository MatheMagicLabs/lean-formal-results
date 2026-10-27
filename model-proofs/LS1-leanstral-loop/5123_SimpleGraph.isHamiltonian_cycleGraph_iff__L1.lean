/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.isHamiltonian_cycleGraph_iff
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean, line 392
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  LS1-leanstral-loop, arm L1, verified in round 1 (round 0 = first attempt)
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
  constructor
  · intro h
    by_cases h1 : n = 1
    · left; exact h1
    · by_cases h0 : n = 0
      · subst h0; exact (not_isHamiltonian_of_isEmpty (G := cycleGraph 0) h).elim
      · by_cases h2 : n = 2
        · subst h2
          have hcard2 : Fintype.card (Fin 2) = 2 := by simp
          exact (not_isHamiltonian_of_card_eq_two hcard2 h).elim
        · have h3le : 3 ≤ n := by
            by_contra! hlt
            have h_cases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
            rcases h_cases with (h0' | h1' | h2')
            · exact h0 h0'
            · exact h1 h1'
            · exact h2 h2'
          right; exact h3le
  · rintro (rfl | h)
    · apply IsHamiltonian.of_card_eq_one; simp
    · exact isHamiltonian_cycleGraph h
