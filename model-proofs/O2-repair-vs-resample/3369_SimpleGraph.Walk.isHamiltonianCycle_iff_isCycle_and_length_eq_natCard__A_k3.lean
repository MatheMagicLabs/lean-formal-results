/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq_natCard
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean, line 273
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem isHamiltonianCycle_iff_isCycle_and_length_eq_natCard :
    p.IsHamiltonianCycle ↔ p.IsCycle ∧ p.length = Nat.card α := by
  rcases finite_or_infinite α with hfin | hinf
  · cases nonempty_fintype α
    rw [Nat.card_eq_fintype_card]
    exact isHamiltonianCycle_iff_isCycle_and_length_eq
  · refine iff_of_false not_isHamiltonianCycle_of_infinite ?_
    rintro ⟨h, h0⟩
    rw [Nat.card_eq_zero_of_infinite] at h0
    have := h.three_le_length
    omega
