/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     HasUniqueRoots.mk'
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Torsion.lean, line 26
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

variable {M : Type*} [CommMonoidWithZero M]

theorem HasUniqueRoots.mk' [IsReduced M]
    (ih : ∀ x ≠ 0, ∀ y ≠ 0, ∀ n ≠ 0, (x ^ n : M) = y ^ n → x = y) :
    HasUniqueRoots M := by
  constructor
  intro n hn x y h
  by_cases hx : x = 0
  · subst x
    exact (eq_zero_of_pow_eq_zero (by simpa [zero_pow hn] using h.symm)).symm
  by_cases hy : y = 0
  · subst y
    exact eq_zero_of_pow_eq_zero (by simpa [zero_pow hn] using h)
  exact ih x hx y hy n hn h
