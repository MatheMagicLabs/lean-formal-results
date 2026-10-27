/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.sum_log_add_one_eq_log_factorial
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Log/Sum.lean, line 43
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem sum_log_add_one_eq_log_factorial : ∑ n ∈ range N, log (n + 1) = log N.factorial := by
  rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod, log_prod]
  · simp
  · intro i _
    positivity
