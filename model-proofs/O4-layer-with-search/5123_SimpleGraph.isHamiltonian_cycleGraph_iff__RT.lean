/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.isHamiltonian_cycleGraph_iff
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean, line 392
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
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
    rcases n with _ | _ | _ | n
    · exfalso
      obtain ⟨a, _⟩ := h (by simp)
      exact a.elim0
    · left; rfl
    · exfalso
      obtain ⟨a, p, hp⟩ := h (by simp)
      have h1 := hp.length_eq
      have h2 := hp.isCycle.three_le_length
      simp only [Fintype.card_fin] at h1
      omega
    · right; omega
  · rintro (rfl | hn)
    · intro h; simp at h
    · exact isHamiltonian_cycleGraph hn
