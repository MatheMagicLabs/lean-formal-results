/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ValueDistribution.truncatedLogCounting_monotoneOn
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Truncated.lean, line 114
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
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

theorem truncatedLogCounting_monotoneOn :
    MonotoneOn (truncatedLogCounting f a) (Set.Ioi 0) := by
  induction a using WithTop.recTopCoe with
  | top =>
    simp only [truncatedLogCounting_top]
    first
    | exact locallyFinsuppWithin.logCounting_monotoneOn
    | (apply locallyFinsuppWithin.logCounting_monotoneOn
       all_goals first | positivity | simp | (intro x; simp) | (intro x; simp [le_min_iff]))
    | (apply locallyFinsuppWithin.logCounting_mono
       all_goals first | positivity | simp | (intro x; simp) | (intro x; simp [le_min_iff]))
  | coe a =>
    simp only [truncatedLogCounting_coe]
    first
    | exact locallyFinsuppWithin.logCounting_monotoneOn
    | (apply locallyFinsuppWithin.logCounting_monotoneOn
       all_goals first | positivity | simp | (intro x; simp) | (intro x; simp [le_min_iff]))
    | (apply locallyFinsuppWithin.logCounting_mono
       all_goals first | positivity | simp | (intro x; simp) | (intro x; simp [le_min_iff]))
