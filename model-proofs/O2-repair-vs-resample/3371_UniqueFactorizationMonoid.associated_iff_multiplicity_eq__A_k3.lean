/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     UniqueFactorizationMonoid.associated_iff_multiplicity_eq
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/UniqueFactorizationDomain/Multiplicity.lean, line 194
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma associated_iff_multiplicity_eq {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    Associated a b ↔ ∀ p : R, Prime p → multiplicity p a = multiplicity p b := by
  constructor
  · intro h p hp
    exact le_antisymm ((dvd_iff_multiplicity_le ha hb).1 h.dvd p hp)
      ((dvd_iff_multiplicity_le hb ha).1 h.symm.dvd p hp)
  · intro h
    exact associated_of_dvd_dvd
      ((dvd_iff_multiplicity_le ha hb).2 fun p hp => (h p hp).le)
      ((dvd_iff_multiplicity_le hb ha).2 fun p hp => (h p hp).ge)
