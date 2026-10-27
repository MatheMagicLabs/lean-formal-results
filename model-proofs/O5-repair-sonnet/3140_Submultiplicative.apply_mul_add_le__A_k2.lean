/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Submultiplicative.apply_mul_add_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Subadditive.lean, line 53
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem apply_mul_add_le (k n r) (hbdd : 0 ≤ u n) : u (k * n + r) ≤ u n ^ k * u r := by
  induction k with
  | zero => simp
  | succ k IH =>
    calc u ((k + 1) * n + r) = u (n + (k * n + r)) := by congr 1; ring
      _ ≤ u n * u (k * n + r) := h _ _
      _ ≤ u n * (u n ^ k * u r) := mul_le_mul_of_nonneg_left IH hbdd
      _ = u n ^ (k + 1) * u r := by ring
