/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.Walk.isHamiltonian_iff_finite_and_isPath_and_length_eq
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean, line 162
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem isHamiltonian_iff_finite_and_isPath_and_length_eq :
    p.IsHamiltonian ↔ Finite α ∧ p.IsPath ∧ p.length = Nat.card α - 1 := by
  constructor
  · intro hp
    have := hp.fintype
    exact ⟨hp.finite, hp.isPath, by rw [Nat.card_eq_fintype_card]; exact hp.length_eq⟩
  · rintro ⟨hfin, hpath, hlen⟩
    have := Fintype.ofFinite α
    rw [Nat.card_eq_fintype_card] at hlen
    exact isHamiltonian_iff_isPath_and_length_eq.mpr ⟨hpath, hlen⟩
