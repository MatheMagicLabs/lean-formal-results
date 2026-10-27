/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.sum_log_eq_log_factorial
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Log/Sum.lean, line 38
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem sum_log_eq_log_factorial : ∑ n ∈ Ioc 0 N, log n = log N.factorial := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le n), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul]
    · ring
    · positivity
    · exact_mod_cast (Nat.factorial_pos n).ne'
