/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Set.even_ncard_compl_iff'
Source:      Mathlib @ a02a63c2, Mathlib/Data/Set/Card.lean, line 1217
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma even_ncard_compl_iff' (h : Odd (Nat.card α)) (s : Set α) : Even sᶜ.ncard ↔ Odd s.ncard := by
  haveI : Finite α := Nat.finite_of_card_ne_zero (by
    intro h0
    rw [h0] at h
    have := Nat.odd_iff.mp h
    omega)
  rw [← ncard_add_ncard_compl s, Nat.odd_add] at h
  exact h.symm
