/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     HasUniqueRoots.mk'
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Torsion.lean, line 26
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem HasUniqueRoots.mk' [IsReduced M]
    (ih : ∀ x ≠ 0, ∀ y ≠ 0, ∀ n ≠ 0, (x ^ n : M) = y ^ n → x = y) :
    HasUniqueRoots M := by
  have key : ∀ n : ℕ, n ≠ 0 → ∀ x y : M, x ^ n = y ^ n → x = y := by
    intro n hn x y h
    by_cases hx : x = 0
    · subst hx
      rw [zero_pow hn] at h
      exact (IsNilpotent.eq_zero ⟨n, h.symm⟩).symm
    by_cases hy : y = 0
    · subst hy
      rw [zero_pow hn] at h
      exact IsNilpotent.eq_zero ⟨n, h⟩
    exact ih x hx y hy n hn h
  constructor
  first
    | exact fun n hn x y h => key n hn x y h
    | exact fun {n} hn x y h => key n hn x y h
    | exact fun x y n hn h => key n hn x y h
    | exact fun {x y n} hn h => key n hn x y h
    | exact fun {x y} n hn h => key n hn x y h
    | exact fun n hn x y => ⟨key n hn x y, fun h => h ▸ rfl⟩
    | exact fun {n} hn x y => ⟨key n hn x y, fun h => h ▸ rfl⟩
