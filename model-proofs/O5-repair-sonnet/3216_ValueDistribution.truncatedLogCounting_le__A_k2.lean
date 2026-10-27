/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ValueDistribution.truncatedLogCounting_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Truncated.lean, line 102
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem truncatedLogCounting_le {r : ℝ} (hr : 1 ≤ r) :
    truncatedLogCounting f a r ≤ logCounting f a r := by
  induction a using WithTop.recTopCoe with
  | top =>
    first
      | exact logCounting_truncate_le _ hr
      | (rw [truncatedLogCounting_top, logCounting_top]
         exact logCounting_truncate_le _ hr)
  | coe a₀ =>
    first
      | exact logCounting_truncate_le _ hr
      | (rw [truncatedLogCounting_coe, logCounting_coe]
         exact logCounting_truncate_le _ hr)
