/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_forall_mem_support
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean, line 261
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem isHamiltonianCycle_iff_isCycle_and_forall_mem_support :
    p.IsHamiltonianCycle ↔ p.IsCycle ∧ ∀ v, v ∈ p.support := by
  constructor
  · intro hp
    exact ⟨hp.isCycle, hp.mem_support⟩
  · rintro ⟨hc, hm⟩
    refine ⟨hc, ?_⟩
    have hpath : p.tail.IsPath := IsPath.mk' (by
      simpa [support_tail_of_not_nil p hc.not_nil] using hc.support_nodup)
    refine hpath.isHamiltonian_of_mem fun w => ?_
    by_cases hw : w = a
    · rw [hw]
      exact p.tail.end_mem_support
    · have := hm w
      rw [← cons_support_tail hc.not_nil] at this
      simpa [hw] using this
