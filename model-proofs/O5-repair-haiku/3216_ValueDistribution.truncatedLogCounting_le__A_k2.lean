/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ValueDistribution.truncatedLogCounting_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Truncated.lean, line 102
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-haiku, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-haiku-4-5
Setup:       Haiku 4.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem truncatedLogCounting_le {r : ℝ} (hr : 1 ≤ r) :
    truncatedLogCounting f a r ≤ logCounting f a r := by
  cases a with
  | top => exact logCounting_truncate_le _ hr
  | coe a₀ => exact logCounting_truncate_le _ hr
