/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Irreducible.multiplicity_eq_ite
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Multiplicity.lean, line 516
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem Irreducible.multiplicity_eq_ite (p : α) {q : α} [Decidable (Associated p q)]
    (hq : Irreducible q) : multiplicity p q = if Associated p q then 1 else 0 := by
  by_cases h : Associated p q
  · rw [if_pos h, ← multiplicity_eq_of_associated_left h, hq.multiplicity_self]
  · rw [if_neg h]
    by_cases hp : IsUnit p
    · exact multiplicity_of_isUnit_left hp q
    · by_cases hd : p ∣ q
      · exfalso
        obtain ⟨c, hc⟩ := hd
        rcases hq.isUnit_or_isUnit hc with hp' | ⟨u, hu⟩
        · exact hp hp'
        · exact h ⟨u, by rw [hu]; exact hc.symm⟩
      · exact multiplicity_eq_zero_of_not_dvd hd
