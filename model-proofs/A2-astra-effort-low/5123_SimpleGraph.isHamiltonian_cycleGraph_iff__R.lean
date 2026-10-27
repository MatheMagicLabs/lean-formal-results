/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.isHamiltonian_cycleGraph_iff
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean, line 392
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
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
  by_cases h : 3 ≤ n
  · simp only [h, or_true, iff_true]
    first
    | exact isHamiltonian_cycleGraph h
    | exact cycleGraph_isHamiltonian h
    | exact isHamiltonian_cycleGraph_of_three_le h
    | exact cycleGraph.isHamiltonian h
    | haveI : Fact (3 ≤ n) := ⟨h⟩
      simpa using (inferInstance : (cycleGraph n).IsHamiltonian)
  · have hn : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hn with rfl | rfl | rfl <;>
      first
      | solve | simp
      | solve | decide
      | solve | simp [SimpleGraph.IsHamiltonian, cycleGraph]
      | 
        simp [SimpleGraph.IsHamiltonian, cycleGraph]
        constructor <;> intro p hp <;>
          (have hlen := hp.isCycle.three_le_length
           have hnodup : p.support.tail.Nodup := by
             first
             | exact hp.isCycle.nodup
             | exact hp.isCycle.support_nodup
             | exact hp.isCycle.2
           have hbound := hnodup.length_le_card
           simp at hbound
           omega)
