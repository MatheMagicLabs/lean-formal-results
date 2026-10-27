/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ValueDistribution.truncatedLogCounting_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Truncated.lean, line 102
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Filter Function MeromorphicOn Metric Real Set
namespace Function.locallyFinsuppWithin
variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
end Function.locallyFinsuppWithin
namespace ValueDistribution
open locallyFinsuppWithin
variable
variable (f a) in
attribute [local simp] truncatedLogCounting_top truncatedLogCounting_coe

theorem truncatedLogCounting_le {r : ℝ} (hr : 1 ≤ r) :
    truncatedLogCounting f a r ≤ logCounting f a r := by
  induction a using WithTop.recTopCoe with
  | top =>
    rw [ValueDistribution.truncatedLogCounting_top, ValueDistribution.logCounting_top]
    exact Function.locallyFinsuppWithin.logCounting_truncate_le _ hr
  | coe a₀ =>
    rw [ValueDistribution.truncatedLogCounting_coe]
    first
      | rw [ValueDistribution.logCounting_coe]
      | simp only [ValueDistribution.logCounting]
    first
      | exact Function.locallyFinsuppWithin.logCounting_truncate_le _ hr
      | (simp only [WithTop.some_eq_coe] at *;
         exact Function.locallyFinsuppWithin.logCounting_truncate_le _ hr)
      | exact Function.locallyFinsuppWithin.logCounting_truncate_le (divisor (f · - a₀) Set.univ)⁺ hr
