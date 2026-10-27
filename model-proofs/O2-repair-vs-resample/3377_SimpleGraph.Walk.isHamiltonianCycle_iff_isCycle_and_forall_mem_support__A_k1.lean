/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_forall_mem_support
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean, line 261
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem isHamiltonianCycle_iff_isCycle_and_forall_mem_support :
    p.IsHamiltonianCycle ↔ p.IsCycle ∧ ∀ v, v ∈ p.support := by
  refine ⟨fun hp ↦ ⟨hp.isCycle, hp.mem_support⟩, fun ⟨hc, hm⟩ ↦ ⟨hc, ?_⟩⟩
  intro v
  have hnd : p.tail.support.Nodup := by
    rw [support_tail_of_not_nil _ hc.not_nil]
    exact hc.support_nodup
  have hmem : v ∈ p.tail.support := by
    by_cases h : v = a
    · rw [h]
      exact p.tail.end_mem_support
    · have := hm v
      rw [support_eq_cons] at this
      rw [support_tail_of_not_nil _ hc.not_nil]
      exact (List.mem_cons.mp this).resolve_left h
  exact le_antisymm (List.nodup_iff_count_le_one.1 hnd v) (List.count_pos_iff.2 hmem)
