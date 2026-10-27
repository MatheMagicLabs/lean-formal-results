/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.isHamiltonian_cycleGraph_iff
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean, line 392
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
  have h₀ : ¬ (cycleGraph 0).IsHamiltonian := by
    first
    | decide
    | simp [IsHamiltonian]
  have h₂ : ¬ (cycleGraph 2).IsHamiltonian := by
    first
    | decide
    | exact not_isHamiltonian_of_card_eq_two (by simp)
    | simp [IsHamiltonian, Walk.IsHamiltonianCycle]
  constructor
  · intro h
    have hn₀ : n ≠ 0 := by
      rintro rfl
      exact h₀ h
    have hn₂ : n ≠ 2 := by
      rintro rfl
      exact h₂ h
    omega
  · rintro (rfl | hn)
    · first
      | decide
      | exact isHamiltonian_cycleGraph (by decide) (by decide)
      | simp [IsHamiltonian, Walk.IsHamiltonianCycle]
    · first
      | exact isHamiltonian_cycleGraph hn
      | exact isHamiltonian_cycleGraph (by omega) (by omega)
      | exact cycleGraph_isHamiltonian hn
      | exact cycleGraph_isHamiltonian (by omega) (by omega)
