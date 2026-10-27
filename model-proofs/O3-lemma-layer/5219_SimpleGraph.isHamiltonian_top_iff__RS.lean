/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.isHamiltonian_top_iff
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean, line 404
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
    rcases Nat.lt_or_ge (Fintype.card α) 3 with hlt | hge
    · rcases (by omega : Fintype.card α = 0 ∨ Fintype.card α = 1 ∨ Fintype.card α = 2)
        with hc | hc | hc
      · exfalso
        obtain ⟨a, _⟩ := h (by omega)
        haveI := Fintype.card_eq_zero_iff.mp hc
        exact isEmptyElim a
      · left; exact hc
      · exact absurd h (not_isHamiltonian_of_card_eq_two hc)
    · right; exact hge
  · rintro (h | h)
    · exact IsHamiltonian.of_card_eq_one h
    · exact isHamiltonian_top h
