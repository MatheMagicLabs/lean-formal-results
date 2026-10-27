/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Set.even_ncard_compl_iff'
Source:      Mathlib @ a02a63c2, Mathlib/Data/Set/Card.lean, line 1217
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma even_ncard_compl_iff' (h : Odd (Nat.card α)) (s : Set α) : Even sᶜ.ncard ↔ Odd s.ncard := by
  have hfin : Finite α := Nat.finite_of_card_ne_zero
    (by intro h0; rw [h0] at h; simp at h)
  have h2 := ncard_add_ncard_compl s s.toFinite sᶜ.toFinite
  rw [← h2] at h
  exact (Nat.odd_add.mp h).symm
