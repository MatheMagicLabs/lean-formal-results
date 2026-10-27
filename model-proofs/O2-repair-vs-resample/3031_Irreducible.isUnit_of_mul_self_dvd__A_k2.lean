/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Irreducible.isUnit_of_mul_self_dvd
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Prime/Defs.lean, line 114
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem Irreducible.isUnit_of_mul_self_dvd [CommMonoid M] {p a : M} (hp : Irreducible p)
    (ha : a * a ∣ p) : IsUnit a := by
  obtain ⟨c, rfl⟩ := ha
  rcases hp.isUnit_or_isUnit (mul_assoc a a c) with h | h
  · exact h
  · exact isUnit_of_mul_isUnit_left h
