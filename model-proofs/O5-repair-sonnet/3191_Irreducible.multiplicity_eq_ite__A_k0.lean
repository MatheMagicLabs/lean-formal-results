/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Irreducible.multiplicity_eq_ite
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Multiplicity.lean, line 516
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem Irreducible.multiplicity_eq_ite (p : α) {q : α} [Decidable (Associated p q)]
    (hq : Irreducible q) : multiplicity p q = if Associated p q then 1 else 0 := by
  by_cases h : Associated p q
  · rw [if_pos h]
    exact (h.symm.irreducible hq).multiplicity_of_associated h
  · rw [if_neg h]
    by_cases hp : IsUnit p
    · exact multiplicity_of_isUnit_left hp q
    · apply multiplicity_eq_zero_of_not_dvd
      rintro ⟨c, hc⟩
      rcases hq.isUnit_or_isUnit hc with h1 | h1
      · exact hp h1
      · obtain ⟨u, rfl⟩ := h1
        exact h ⟨u, hc.symm⟩
