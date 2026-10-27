/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.isHamiltonian_cycleGraph_iff
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean, line 392
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA3-leanstral-agent-feedback, arm rueck, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent with goal-state feedback (arm rueck)
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
    by_cases hn1 : n = 1
    · exact Or.inl hn1
    · by_cases h3 : 3 ≤ n
      · exact Or.inr h3
      · have hn_lt_3 : n < 3 := by omega
        have h_cases : n = 0 ∨ n = 2 := by omega
        rcases h_cases with (rfl | rfl)
        · have hcard : Fintype.card (Fin 0) ≠ 1 := by
            simp [Fintype.card_fin]
          have hbot : cycleGraph 0 = (⊥ : SimpleGraph (Fin 0)) := cycleGraph_zero_eq_bot
          rw [hbot] at h
          exact absurd h (not_isHamiltonian_bot_of_card_ne_one hcard)
        · have hcard : Fintype.card (Fin 2) = 2 := by
            simp [Fintype.card_fin]
          exact absurd h (not_isHamiltonian_of_card_eq_two hcard)
  · intro h
    rcases h with (rfl | h)
    · have hcard : Fintype.card (Fin 1) = 1 := by
        simp [Fintype.card_fin]
      exact IsHamiltonian.of_card_eq_one hcard
    · exact isHamiltonian_cycleGraph h
