/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.isHamiltonian_top_iff
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean, line 404
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  constructor
  · intro h
    by_cases h₁ : Fintype.card α = 1
    · exact Or.inl h₁
    · obtain ⟨a, p, hp⟩ := h h₁
      exact Or.inr (hp.length_eq ▸ hp.three_le_length)
  · rintro (h | h)
    · exact IsHamiltonian.of_card_eq_one h
    · exact isHamiltonian_top h
