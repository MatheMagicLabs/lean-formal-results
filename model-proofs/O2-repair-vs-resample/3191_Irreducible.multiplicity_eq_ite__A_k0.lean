/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Irreducible.multiplicity_eq_ite
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Multiplicity.lean, line 516
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem Irreducible.multiplicity_eq_ite (p : α) {q : α} [Decidable (Associated p q)]
    (hq : Irreducible q) : multiplicity p q = if Associated p q then 1 else 0 := by
  split_ifs with h
  · exact (h.symm.irreducible hq).multiplicity_of_associated h
  · by_cases hp : IsUnit p
    · exact multiplicity_of_isUnit_left hp q
    · apply multiplicity_eq_zero_of_not_dvd
      rintro ⟨c, rfl⟩
      rcases hq.isUnit_or_isUnit rfl with hpu | hcu
      · exact hp hpu
      · exact h ⟨hcu.unit, by simp⟩
