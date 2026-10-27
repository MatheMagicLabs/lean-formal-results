/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ValueDistribution.truncatedLogCounting_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Truncated.lean, line 102
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem truncatedLogCounting_le {r : ℝ} (hr : 1 ≤ r) :
    truncatedLogCounting f a r ≤ logCounting f a r := by
  induction a using WithTop.recTopCoe with
  | top =>
    first
      | (rw [truncatedLogCounting_top, logCounting_top]
         exact logCounting_truncate_le _ hr)
      | exact logCounting_truncate_le (divisor f Set.univ)⁻ hr
  | coe a₀ =>
    first
      | (rw [truncatedLogCounting_coe, logCounting_coe]
         exact logCounting_truncate_le _ hr)
      | exact logCounting_truncate_le (divisor (f · - a₀) Set.univ)⁺ hr
