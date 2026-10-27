/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.isHamiltonian_top_iff
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean, line 404
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[simp]
theorem isHamiltonian_top_iff :
    (completeGraph α).IsHamiltonian ↔ Fintype.card α = 1 ∨ 3 ≤ Fintype.card α := by
  refine ⟨fun h ↦ ?_, (·.elim IsHamiltonian.of_card_eq_one isHamiltonian_top)⟩
  by_contra hc
  push_neg at hc
  rcases show Fintype.card α = 0 ∨ Fintype.card α = 2 by lia with h0 | h2
  · have : IsEmpty α := Fintype.card_eq_zero_iff.mp h0
    exact not_isHamiltonian_of_isEmpty h
  · exact not_isHamiltonian_of_card_eq_two h2 h
