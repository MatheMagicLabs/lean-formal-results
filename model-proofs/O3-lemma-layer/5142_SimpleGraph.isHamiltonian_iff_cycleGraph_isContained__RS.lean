/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.isHamiltonian_iff_cycleGraph_isContained
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean, line 381
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
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

theorem isHamiltonian_iff_cycleGraph_isContained (h : 3 ≤ Fintype.card α) :
    G.IsHamiltonian ↔ cycleGraph (Fintype.card α) ⊑ G := by
  constructor
  · intro hG
    have hne : Fintype.card α ≠ 1 := by omega
    obtain ⟨a, p, hp⟩ := hG hne
    rw [cycleGraph_isContained_iff (by omega)]
    exact ⟨a, p, hp.isCycle, hp.length_eq⟩
  · rw [cycleGraph_isContained_iff (by omega)]
    rintro ⟨v, p, hc, hl⟩ _
    refine ⟨v, p, ?_⟩
    rw [Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one]
    refine ⟨hc, fun w => ?_⟩
    have hnd := hc.support_nodup
    have hlen : p.support.tail.length = Fintype.card α := by simp [hl]
    have huniv : p.support.tail.toFinset = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [List.toFinset_card_of_nodup hnd, hlen]
    have hmem : w ∈ p.support.tail := by
      rw [← List.mem_toFinset, huniv]; exact Finset.mem_univ w
    exact List.count_eq_one_of_mem hnd hmem
