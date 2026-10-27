/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.isHamiltonian_iff_cycleGraph_isContained
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean, line 381
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 3 (round 0 = first attempt)
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

theorem isHamiltonian_iff_cycleGraph_isContained (h : 3 ≤ Fintype.card α) :
    G.IsHamiltonian ↔ cycleGraph (Fintype.card α) ⊑ G := by
  classical
  rw [cycleGraph_isContained_iff h]
  constructor
  · intro hG
    obtain ⟨v, p, hp⟩ := hG (by omega)
    refine ⟨v, p, ?_, ?_⟩
    · first
      | exact hp.isCycle h
      | exact hp.isCycle
    · first
      | exact hp.length_eq_card
      | exact hp.length_eq
      | exact hp.length
  · rintro ⟨v, p, hp, hlen⟩
    intro _
    refine ⟨v, p, ?_⟩
    first
    | exact (hp.isHamiltonianCycle_iff_length_eq).2 hlen
    | exact (hp.isHamiltonianCycle_iff_length_eq_card).2 hlen
    | exact (Walk.isHamiltonianCycle_iff_isCycle_and_length_eq h).2 ⟨hp, hlen⟩
    | exact (Walk.isHamiltonianCycle_iff_isCycle_and_length_eq).2 ⟨hp, hlen⟩
    | exact (Walk.isHamiltonianCycle_iff_isCycle_and_length_eq_card h).2 ⟨hp, hlen⟩
    | exact (Walk.isHamiltonianCycle_iff_isCycle_and_length_eq_card).2 ⟨hp, hlen⟩
    | exact hp.isHamiltonianCycle_of_card_le_length hlen.ge
    | exact hp.isHamiltonianCycle_of_length_ge hlen.ge
