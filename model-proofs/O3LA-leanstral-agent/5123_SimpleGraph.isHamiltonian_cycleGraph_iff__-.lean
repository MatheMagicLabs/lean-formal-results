/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.isHamiltonian_cycleGraph_iff
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean, line 392
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA-leanstral-agent, arm -, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 as a tool-using agent (Mistral Vibe)
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
    · have hcard_ne_one : Fintype.card (Fin n) ≠ 1 := by
        rw [Fintype.card_fin]
        exact hn1
      rcases h hcard_ne_one with ⟨a, p, hp⟩
      have hlen := hp.length_eq
      have h3len := hp.three_le_length
      rw [Fintype.card_fin] at hlen
      have : 3 ≤ n := h3len.trans_eq hlen
      exact Or.inr this
  · intro h
    rcases h with (hn1 | hn3)
    · subst hn1
      simp [SimpleGraph.IsHamiltonian]
    · exact isHamiltonian_cycleGraph hn3
