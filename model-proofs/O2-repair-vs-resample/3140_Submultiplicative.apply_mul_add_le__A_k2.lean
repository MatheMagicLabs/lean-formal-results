/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Submultiplicative.apply_mul_add_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Subadditive.lean, line 53
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem apply_mul_add_le (k n r) (hbdd : 0 ≤ u n) : u (k * n + r) ≤ u n ^ k * u r := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : (k + 1) * n + r = n + (k * n + r) := by ring
    rw [e]
    calc u (n + (k * n + r)) ≤ u n * u (k * n + r) := h n (k * n + r)
      _ ≤ u n * (u n ^ k * u r) := mul_le_mul_of_nonneg_left ih hbdd
      _ = u n ^ (k + 1) * u r := by ring
